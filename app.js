'use strict';

const DB_NAME = 'entry-vault-db';
const DB_VERSION = 2;
const STORE_NAME = 'records';
const SECURITY_STORE_NAME = 'security';
const KEY_SALT = 'entryVault.salt';
const KEY_VERIFIER = 'entryVault.verifier';
const KEY_BIOMETRIC = 'entryVault.biometric';
const BIOMETRIC_VERSION = 2;
const BIOMETRIC_KEY_RECORD_ID = 'biometric-wrapping-key';
const AUTO_LOCK_MS = 15 * 60 * 1000;
const PBKDF2_ITERATIONS = 250000;

const state = {
  db: null,
  cryptoKey: null,
  records: [],
  imageData: '',
  ocrText: '',
  editingId: '',
  dialogId: '',
  lockTimer: null,
  deferredInstallPrompt: null,
  toastTimer: null,
  biometricUnlockInProgress: false,
  autoBiometricAttempted: false
};

const $ = (selector) => document.querySelector(selector);
const $$ = (selector) => [...document.querySelectorAll(selector)];
const encoder = new TextEncoder();
const decoder = new TextDecoder();

function bytesToBase64(bytes) {
  let binary = '';
  const chunk = 0x8000;
  for (let i = 0; i < bytes.length; i += chunk) {
    binary += String.fromCharCode(...bytes.subarray(i, i + chunk));
  }
  return btoa(binary);
}

function base64ToBytes(base64) {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i += 1) bytes[i] = binary.charCodeAt(i);
  return bytes;
}

function bytesToBase64Url(bytes) {
  return bytesToBase64(bytes)
    .replaceAll('+', '-')
    .replaceAll('/', '_')
    .replace(/=+$/g, '');
}

function base64UrlToBytes(base64Url) {
  const normalized = String(base64Url).replaceAll('-', '+').replaceAll('_', '/');
  const padding = '='.repeat((4 - (normalized.length % 4)) % 4);
  return base64ToBytes(normalized + padding);
}

function toUint8Array(value) {
  if (value instanceof Uint8Array) return new Uint8Array(value);
  if (ArrayBuffer.isView(value)) {
    return new Uint8Array(value.buffer.slice(value.byteOffset, value.byteOffset + value.byteLength));
  }
  if (value instanceof ArrayBuffer) return new Uint8Array(value.slice(0));
  if (value && typeof value.byteLength === 'number') {
    const source = value.buffer || value;
    const offset = Number(value.byteOffset || 0);
    return new Uint8Array(source.slice(offset, offset + value.byteLength));
  }
  throw new TypeError('Expected an ArrayBuffer or TypedArray');
}

function randomBytes(length = 32) {
  return crypto.getRandomValues(new Uint8Array(length));
}

function escapeHtml(value = '') {
  return String(value)
    .replaceAll('&', '&amp;')
    .replaceAll('<', '&lt;')
    .replaceAll('>', '&gt;')
    .replaceAll('"', '&quot;')
    .replaceAll("'", '&#039;');
}

function normalizeSearch(value = '') {
  return String(value)
    .normalize('NFKC')
    .toLocaleLowerCase('ja')
    .replace(/[\s\u3000・･,，.．/／\\\-_ー―‐:：()（）\[\]【】]/g, '');
}

function formatDate(iso) {
  if (!iso) return '';
  const d = new Date(iso);
  return new Intl.DateTimeFormat('ja-JP', {
    year: 'numeric', month: '2-digit', day: '2-digit',
    hour: '2-digit', minute: '2-digit'
  }).format(d);
}

function showToast(message) {
  const toast = $('#toast');
  toast.textContent = message;
  toast.classList.add('show');
  clearTimeout(state.toastTimer);
  state.toastTimer = setTimeout(() => toast.classList.remove('show'), 2600);
}

function setBusy(button, busy, busyText = '処理中…') {
  if (!button) return;
  if (busy) {
    button.dataset.originalText = button.textContent;
    button.textContent = busyText;
    button.disabled = true;
  } else {
    button.textContent = button.dataset.originalText || button.textContent;
    button.disabled = false;
  }
}

function hasVault() {
  return Boolean(localStorage.getItem(KEY_SALT) && localStorage.getItem(KEY_VERIFIER));
}

function getBiometricConfig() {
  try {
    const config = JSON.parse(localStorage.getItem(KEY_BIOMETRIC) || 'null');
    if (!config || ![1, BIOMETRIC_VERSION].includes(config.version) || !config.credentialId || !config.wrappedKey) {
      return null;
    }
    const mode = config.mode || (config.prfSalt ? 'prf' : 'device');
    if (mode === 'prf' && !config.prfSalt) return null;
    if (mode === 'device' && !config.keyRecordId) return null;
    return { ...config, mode };
  } catch (_) {
    return null;
  }
}

function hasBiometricUnlock() {
  return Boolean(hasVault() && getBiometricConfig());
}

function isWebAuthnAvailable() {
  return Boolean(
    window.isSecureContext &&
    window.PublicKeyCredential &&
    navigator.credentials?.create &&
    navigator.credentials?.get
  );
}

async function platformAuthenticatorAvailable() {
  if (!isWebAuthnAvailable()) return false;
  if (typeof PublicKeyCredential.isUserVerifyingPlatformAuthenticatorAvailable !== 'function') return true;
  try {
    return await PublicKeyCredential.isUserVerifyingPlatformAuthenticatorAvailable();
  } catch (_) {
    return false;
  }
}

async function importAesKey(rawBytes, extractable = false) {
  return crypto.subtle.importKey(
    'raw',
    rawBytes,
    { name: 'AES-GCM', length: 256 },
    extractable,
    ['encrypt', 'decrypt']
  );
}

async function verifyVaultKey(key) {
  const verifierText = localStorage.getItem(KEY_VERIFIER);
  if (!verifierText) throw new Error('Vault verifier is missing');
  const result = await decryptObject(JSON.parse(verifierText), key);
  if (result.marker !== 'ENTRY_VAULT_V1') throw new Error('Invalid verifier');
}

function getPrfResult(credential) {
  const value = credential?.getClientExtensionResults?.()?.prf?.results?.first;
  return value ? toUint8Array(value) : null;
}

function publicKeyCredentialDescriptor(config) {
  const descriptor = {
    type: 'public-key',
    id: base64UrlToBytes(config.credentialId)
  };
  if (Array.isArray(config.transports) && config.transports.length) {
    descriptor.transports = config.transports;
  }
  return descriptor;
}

async function requestStandardAssertion(config) {
  const assertion = await navigator.credentials.get({
    publicKey: {
      challenge: randomBytes(32),
      allowCredentials: [publicKeyCredentialDescriptor(config)],
      userVerification: 'required',
      timeout: 60000
    }
  });

  if (!assertion) throw new Error('Authentication was not completed');
  const returnedId = bytesToBase64Url(new Uint8Array(assertion.rawId));
  if (returnedId !== config.credentialId) throw new Error('Credential mismatch');
  return assertion;
}

async function requestPrfAssertion(config) {
  const assertion = await navigator.credentials.get({
    publicKey: {
      challenge: randomBytes(32),
      allowCredentials: [publicKeyCredentialDescriptor(config)],
      userVerification: 'required',
      timeout: 60000,
      extensions: {
        prf: {
          evalByCredential: {
            [config.credentialId]: { first: base64ToBytes(config.prfSalt) }
          }
        }
      }
    }
  });

  if (!assertion) throw new Error('Authentication was not completed');
  const returnedId = bytesToBase64Url(new Uint8Array(assertion.rawId));
  if (returnedId !== config.credentialId) throw new Error('Credential mismatch');
  const prfResult = getPrfResult(assertion);
  if (!prfResult || prfResult.byteLength !== 32) throw new Error('PRF result is unavailable');
  return prfResult;
}

async function restoreVaultKeyFromWrappedPayload(config, wrappingKey) {
  const wrapped = await decryptObject(config.wrappedKey, wrappingKey);
  if (!['ENTRY_VAULT_BIOMETRIC_V1', 'ENTRY_VAULT_BIOMETRIC_V2'].includes(wrapped.marker) || !wrapped.rawKey) {
    throw new Error('Invalid biometric key payload');
  }
  const rawVaultKey = base64ToBytes(wrapped.rawKey);
  const vaultKey = await importAesKey(rawVaultKey, false);
  rawVaultKey.fill(0);
  await verifyVaultKey(vaultKey);
  state.cryptoKey = vaultKey;
}

async function unlockVaultWithBiometric() {
  const config = getBiometricConfig();
  if (!config) throw new Error('Biometric configuration is missing');

  if (config.mode === 'prf') {
    const prfResult = await requestPrfAssertion(config);
    const wrappingKey = await importAesKey(prfResult, false);
    prfResult.fill(0);
    await restoreVaultKeyFromWrappedPayload(config, wrappingKey);
    return;
  }

  await requestStandardAssertion(config);
  await ensureDatabase();
  const wrappingKey = await getBiometricWrappingKey(config.keyRecordId);
  if (!wrappingKey) throw new Error('Device wrapping key is missing');
  await restoreVaultKeyFromWrappedPayload(config, wrappingKey);
}

async function deriveKey(password, saltBytes, extractable = false) {
  const keyMaterial = await crypto.subtle.importKey(
    'raw', encoder.encode(password), 'PBKDF2', false, ['deriveKey']
  );
  return crypto.subtle.deriveKey(
    {
      name: 'PBKDF2',
      salt: saltBytes,
      iterations: PBKDF2_ITERATIONS,
      hash: 'SHA-256'
    },
    keyMaterial,
    { name: 'AES-GCM', length: 256 },
    extractable,
    ['encrypt', 'decrypt']
  );
}

async function encryptObject(object, key = state.cryptoKey) {
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const plain = encoder.encode(JSON.stringify(object));
  const encrypted = await crypto.subtle.encrypt({ name: 'AES-GCM', iv }, key, plain);
  return {
    iv: bytesToBase64(iv),
    data: bytesToBase64(new Uint8Array(encrypted))
  };
}

async function decryptObject(payload, key = state.cryptoKey) {
  const iv = base64ToBytes(payload.iv);
  const data = base64ToBytes(payload.data);
  const decrypted = await crypto.subtle.decrypt({ name: 'AES-GCM', iv }, key, data);
  return JSON.parse(decoder.decode(decrypted));
}

async function createVault(password) {
  const salt = crypto.getRandomValues(new Uint8Array(16));
  const key = await deriveKey(password, salt);
  const verifier = await encryptObject({ marker: 'ENTRY_VAULT_V1' }, key);
  localStorage.setItem(KEY_SALT, bytesToBase64(salt));
  localStorage.setItem(KEY_VERIFIER, JSON.stringify(verifier));
  localStorage.removeItem(KEY_BIOMETRIC);
  await deleteBiometricWrappingKey().catch(() => {});
  state.cryptoKey = key;
}

async function unlockVault(password) {
  const saltText = localStorage.getItem(KEY_SALT);
  if (!saltText) throw new Error('Vault salt is missing');
  const key = await deriveKey(password, base64ToBytes(saltText));
  await verifyVaultKey(key);
  state.cryptoKey = key;
}

function openDatabase() {
  return new Promise((resolve, reject) => {
    const request = indexedDB.open(DB_NAME, DB_VERSION);
    request.onupgradeneeded = () => {
      const db = request.result;
      if (!db.objectStoreNames.contains(STORE_NAME)) {
        db.createObjectStore(STORE_NAME, { keyPath: 'id' });
      }
      if (!db.objectStoreNames.contains(SECURITY_STORE_NAME)) {
        db.createObjectStore(SECURITY_STORE_NAME, { keyPath: 'id' });
      }
    };
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

async function ensureDatabase() {
  if (!state.db) state.db = await openDatabase();
  return state.db;
}

function idbRequest(mode, action, storeName = STORE_NAME) {
  return new Promise((resolve, reject) => {
    const tx = state.db.transaction(storeName, mode);
    const store = tx.objectStore(storeName);
    const request = action(store);
    request.onsuccess = () => resolve(request.result);
    request.onerror = () => reject(request.error);
  });
}

async function saveEnvelope(record) {
  const encrypted = await encryptObject(record);
  return idbRequest('readwrite', (store) => store.put({
    id: record.id,
    updatedAt: record.updatedAt,
    encrypted
  }));
}

async function deleteEnvelope(id) {
  return idbRequest('readwrite', (store) => store.delete(id));
}

async function getAllEnvelopes() {
  return idbRequest('readonly', (store) => store.getAll());
}

async function clearAllEnvelopes() {
  return idbRequest('readwrite', (store) => store.clear());
}

async function saveBiometricWrappingKey(key, id = BIOMETRIC_KEY_RECORD_ID) {
  await ensureDatabase();
  return idbRequest('readwrite', (store) => store.put({ id, key }), SECURITY_STORE_NAME);
}

async function getBiometricWrappingKey(id = BIOMETRIC_KEY_RECORD_ID) {
  await ensureDatabase();
  const record = await idbRequest('readonly', (store) => store.get(id), SECURITY_STORE_NAME);
  return record?.key || null;
}

async function deleteBiometricWrappingKey(id = BIOMETRIC_KEY_RECORD_ID) {
  await ensureDatabase();
  return idbRequest('readwrite', (store) => store.delete(id), SECURITY_STORE_NAME);
}

async function loadRecords() {
  const envelopes = await getAllEnvelopes();
  const records = [];
  for (const envelope of envelopes) {
    try {
      records.push(await decryptObject(envelope.encrypted));
    } catch (error) {
      console.warn('Record decrypt failed', envelope.id, error);
    }
  }
  state.records = records.sort((a, b) => new Date(b.updatedAt) - new Date(a.updatedAt));
  renderSearchResults();
  updateRecordCount();
  updateStorageSummary();
}

function configureAuthScreen() {
  const setup = !hasVault();
  const biometricReady = !setup && hasBiometricUnlock() && isWebAuthnAvailable();
  $('#confirmPasswordWrap').hidden = !setup;
  $('#confirmPassword').required = setup;
  $('#biometricUnlockWrap').hidden = !biometricReady;
  $('#authForm').classList.toggle('auth-form-biometric', biometricReady);
  $('#authSubmit').textContent = setup ? '保管庫を作成' : 'マスターパスワードで解除';
  $('#authDescription').textContent = setup
    ? '最初に、保存情報を暗号化するためのマスターパスワードを設定します。'
    : biometricReady
      ? '生体・端末認証、またはマスターパスワードで保存情報を復号します。'
      : 'マスターパスワードを入力して、保存情報を復号します。';
}

async function handleBiometricUnlock({ automatic = false } = {}) {
  if (state.biometricUnlockInProgress || !hasBiometricUnlock()) return;
  const button = $('#biometricUnlockButton');
  const error = $('#authError');
  state.biometricUnlockInProgress = true;
  error.textContent = '';
  setBusy(button, true, '本人確認中…');
  try {
    await unlockVaultWithBiometric();
    await enterApp();
    $('#masterPassword').value = '';
    showToast('生体・端末認証で解除しました');
  } catch (biometricError) {
    console.error(biometricError);
    if (!(automatic && biometricError?.name === 'NotAllowedError')) {
      error.textContent = biometricError?.name === 'NotAllowedError'
        ? '認証がキャンセルされました。もう一度お試しください。'
        : '生体・端末認証を利用できません。マスターパスワードで解除してください。';
    }
  } finally {
    state.biometricUnlockInProgress = false;
    setBusy(button, false);
  }
}

function maybeAutoBiometricUnlock() {
  if (state.autoBiometricAttempted || document.visibilityState !== 'visible' || !hasBiometricUnlock()) return;
  state.autoBiometricAttempted = true;
  setTimeout(() => handleBiometricUnlock({ automatic: true }), 350);
}

async function handleAuthSubmit(event) {
  event.preventDefault();
  const password = $('#masterPassword').value;
  const confirmPassword = $('#confirmPassword').value;
  const setup = !hasVault();
  const error = $('#authError');
  error.textContent = '';

  if (password.length < 8) {
    error.textContent = '8文字以上のパスワードを設定してください。';
    return;
  }
  if (setup && password !== confirmPassword) {
    error.textContent = '確認用パスワードが一致しません。';
    return;
  }

  setBusy($('#authSubmit'), true, setup ? '作成中…' : '解除中…');
  try {
    if (setup) await createVault(password);
    else await unlockVault(password);
    await enterApp();
    $('#masterPassword').value = '';
    $('#confirmPassword').value = '';
  } catch (authError) {
    console.error(authError);
    error.textContent = 'パスワードが正しくありません。';
  } finally {
    setBusy($('#authSubmit'), false);
  }
}

async function enterApp() {
  await ensureDatabase();
  $('#authScreen').hidden = true;
  $('#appShell').hidden = false;
  resetAutoLock();
  await loadRecords();
  await updateBiometricSettings();
}

function lockApp() {
  state.cryptoKey = null;
  state.records = [];
  state.dialogId = '';
  clearTimeout(state.lockTimer);
  if ($('#recordDialog').open) $('#recordDialog').close();
  resetForm();
  $('#appShell').hidden = true;
  $('#authScreen').hidden = false;
  configureAuthScreen();
  $('#authError').textContent = '';
  $('#masterPassword').focus();
}

function resetAutoLock() {
  if (!state.cryptoKey) return;
  clearTimeout(state.lockTimer);
  state.lockTimer = setTimeout(() => {
    lockApp();
    showToast('一定時間操作がなかったためロックしました');
  }, AUTO_LOCK_MS);
}

function switchView(viewId) {
  $$('.view').forEach((view) => view.classList.toggle('active', view.id === viewId));
  $$('.nav-button').forEach((button) => button.classList.toggle('active', button.dataset.view === viewId));
  if (viewId === 'searchView') renderSearchResults();
  if (viewId === 'settingsView') {
    updateStorageSummary();
    updateBiometricSettings();
  }
  window.scrollTo({ top: 0, behavior: 'smooth' });
}

async function compressImage(file, maxSide = 1800, quality = 0.86) {
  const dataUrl = await new Promise((resolve, reject) => {
    const reader = new FileReader();
    reader.onload = () => resolve(reader.result);
    reader.onerror = () => reject(reader.error);
    reader.readAsDataURL(file);
  });

  const image = await loadImage(dataUrl);
  const scale = Math.min(1, maxSide / Math.max(image.naturalWidth, image.naturalHeight));
  const canvas = document.createElement('canvas');
  canvas.width = Math.max(1, Math.round(image.naturalWidth * scale));
  canvas.height = Math.max(1, Math.round(image.naturalHeight * scale));
  canvas.getContext('2d', { alpha: false }).drawImage(image, 0, 0, canvas.width, canvas.height);
  return canvas.toDataURL('image/jpeg', quality);
}

function loadImage(src) {
  return new Promise((resolve, reject) => {
    const image = new Image();
    image.onload = () => resolve(image);
    image.onerror = reject;
    image.src = src;
  });
}

async function prepareOcrImage(dataUrl) {
  const image = await loadImage(dataUrl);
  const minimumWidth = 1800;
  const scale = image.naturalWidth < minimumWidth ? Math.min(2, minimumWidth / image.naturalWidth) : 1;
  const canvas = document.createElement('canvas');
  canvas.width = Math.round(image.naturalWidth * scale);
  canvas.height = Math.round(image.naturalHeight * scale);
  const ctx = canvas.getContext('2d', { willReadFrequently: true });
  ctx.drawImage(image, 0, 0, canvas.width, canvas.height);

  const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
  const d = imageData.data;
  for (let i = 0; i < d.length; i += 4) {
    const gray = 0.299 * d[i] + 0.587 * d[i + 1] + 0.114 * d[i + 2];
    const contrasted = Math.max(0, Math.min(255, (gray - 128) * 1.28 + 128));
    d[i] = d[i + 1] = d[i + 2] = contrasted;
  }
  ctx.putImageData(imageData, 0, 0);
  return canvas.toDataURL('image/jpeg', 0.92);
}

function pixelLuminance(data, offset) {
  return 0.299 * data[offset] + 0.587 * data[offset + 1] + 0.114 * data[offset + 2];
}

function sampledMedian(values) {
  if (!values.length) return 128;
  values.sort((a, b) => a - b);
  return values[Math.floor(values.length / 2)];
}

function findDeliveryNameCrop(sourceCanvas) {
  const { width, height } = sourceCanvas;
  const ctx = sourceCanvas.getContext('2d', { willReadFrequently: true });
  const pixels = ctx.getImageData(0, 0, width, height).data;
  const luminanceAt = (x, y) => pixelLuminance(pixels, (y * width + x) * 4);

  const dividerLeft = Math.round(width * 0.02);
  const dividerRight = Math.round(width * 0.98);
  const dividerTop = Math.round(height * 0.08);
  const dividerBottom = Math.round(height * 0.25);
  const backgroundSamples = [];

  for (let y = dividerTop; y < dividerBottom; y += 8) {
    for (let x = dividerLeft; x < dividerRight; x += 12) {
      backgroundSamples.push(luminanceAt(x, y));
    }
  }

  const background = sampledMedian(backgroundSamples);
  const darkMode = background < 128;
  let dividerY = Math.round(height * 0.163);
  let foundDivider = false;

  for (let y = dividerTop; y < dividerBottom; y += 1) {
    let dividerPixels = 0;
    let samples = 0;
    for (let x = dividerLeft; x < dividerRight; x += 4) {
      const value = luminanceAt(x, y);
      const isDivider = darkMode
        ? value > background + 6 && value < 120
        : value < background - 6 && value > 135;
      if (isDivider) dividerPixels += 1;
      samples += 1;
    }
    if (samples && dividerPixels / samples > 0.72) {
      dividerY = y;
      foundDivider = true;
    }
  }

  if (!foundDivider) dividerY = Math.round(height * 0.163);

  const textLeft = Math.round(width * 0.02);
  const textRight = Math.round(width * 0.70);
  const scanTop = Math.min(height - 1, dividerY + 5);
  const scanBottom = Math.min(height, dividerY + Math.round(height * 0.18));
  const textBackgroundSamples = [];

  for (let y = scanTop; y < scanBottom; y += 8) {
    for (let x = textLeft; x < textRight; x += 12) {
      textBackgroundSamples.push(luminanceAt(x, y));
    }
  }

  const textBackground = sampledMedian(textBackgroundSamples);
  const textRows = [];
  for (let y = scanTop; y < scanBottom; y += 1) {
    let textPixels = 0;
    let samples = 0;
    for (let x = textLeft; x < textRight; x += 2) {
      const value = luminanceAt(x, y);
      const isText = darkMode
        ? value > Math.max(120, textBackground + 55)
        : value < Math.min(135, textBackground - 55);
      if (isText) textPixels += 1;
      samples += 1;
    }
    textRows.push({ y, active: samples && textPixels / samples > 0.008 });
  }

  const groups = [];
  let start = null;
  let lastActive = null;
  for (const row of textRows) {
    if (row.active) {
      if (start === null) start = row.y;
      lastActive = row.y;
    } else if (start !== null && row.y - lastActive > 3) {
      groups.push({ start, end: lastActive });
      start = null;
      lastActive = null;
    }
  }
  if (start !== null) groups.push({ start, end: lastActive });

  const minimumNameHeight = Math.max(12, Math.round(height * 0.014));
  const nameGroup = groups.find((group) => group.end - group.start + 1 >= minimumNameHeight);
  const fallbackTop = dividerY + Math.round(height * 0.012);
  const fallbackBottom = dividerY + Math.round(height * 0.075);
  const top = Math.max(0, (nameGroup?.start ?? fallbackTop) - Math.round(height * 0.005));
  const bottom = Math.min(height, (nameGroup?.end ?? fallbackBottom) + Math.round(height * 0.005));

  return {
    left: textLeft,
    top,
    width: Math.max(1, textRight - textLeft),
    height: Math.max(1, bottom - top),
    darkMode
  };
}

async function prepareDeliveryNameOcrImage(dataUrl) {
  const image = await loadImage(dataUrl);
  const sourceCanvas = document.createElement('canvas');
  sourceCanvas.width = image.naturalWidth;
  sourceCanvas.height = image.naturalHeight;
  const sourceCtx = sourceCanvas.getContext('2d', { willReadFrequently: true });
  sourceCtx.drawImage(image, 0, 0);

  const crop = findDeliveryNameCrop(sourceCanvas);
  const targetHeight = 260;
  const scale = Math.min(4, Math.max(2, targetHeight / crop.height));
  const canvas = document.createElement('canvas');
  canvas.width = Math.max(1, Math.round(crop.width * scale));
  canvas.height = Math.max(1, Math.round(crop.height * scale));
  const ctx = canvas.getContext('2d', { willReadFrequently: true });
  ctx.drawImage(
    sourceCanvas,
    crop.left, crop.top, crop.width, crop.height,
    0, 0, canvas.width, canvas.height
  );

  const imageData = ctx.getImageData(0, 0, canvas.width, canvas.height);
  const data = imageData.data;
  for (let i = 0; i < data.length; i += 4) {
    let gray = pixelLuminance(data, i);
    if (crop.darkMode) gray = 255 - gray;
    const contrasted = Math.max(0, Math.min(255, (gray - 128) * 1.42 + 128));
    data[i] = data[i + 1] = data[i + 2] = contrasted;
  }
  ctx.putImageData(imageData, 0, 0);
  return canvas.toDataURL('image/png');
}

async function handleScreenshot(file) {
  if (!file) return;
  if (!file.type.startsWith('image/')) {
    showToast('画像ファイルを選択してください');
    return;
  }
  try {
    state.imageData = await compressImage(file);
    $('#imagePreview').src = state.imageData;
    $('#imagePreviewWrap').hidden = false;
    $('#ocrButton').disabled = false;
    $('#ocrDetails').hidden = true;
    state.ocrText = '';
  } catch (error) {
    console.error(error);
    showToast('画像を読み込めませんでした');
  }
}

function removeImage() {
  state.imageData = '';
  state.ocrText = '';
  $('#screenshotInput').value = '';
  $('#imagePreview').removeAttribute('src');
  $('#imagePreviewWrap').hidden = true;
  $('#ocrButton').disabled = true;
  $('#ocrDetails').hidden = true;
  $('#ocrRawText').value = '';
}

function cleanOcrLine(line) {
  return line
    .normalize('NFKC')
    .replace(/[|｜]/g, ' ')
    .replace(/^[\s•●・･※*#]+|[\s•●・･※*#]+$/g, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function valueAfterLabel(lines, labels) {
  const anyFieldLabel = /^(?:お名前|氏名|名前|宛名|受取人|お届け先名|届け先名|顧客名|ご依頼主|建物名|マンション名|アパート名|ビル名|施設名|物件名|部屋番号|部屋No\.?|室番号|Room|暗証番号|暗証|PIN|メモ)\s*[:：]?/i;
  for (let i = 0; i < lines.length; i += 1) {
    const line = lines[i];
    for (const label of labels) {
      const pattern = new RegExp(`(?:${label})\\s*[:：]?\\s*(.*)$`, 'i');
      const match = line.match(pattern);
      if (!match) continue;
      const sameLineValue = (match[1] || '').trim();
      if (sameLineValue) return sameLineValue;
      const nextLine = (lines[i + 1] || '').trim();
      if (nextLine && !anyFieldLabel.test(nextLine)) return nextLine;
    }
  }
  return '';
}

function extractDeliveryName(rawText) {
  const lines = rawText
    .normalize('NFKC')
    .replace(/\r/g, '')
    .split('\n')
    .map(cleanOcrLine)
    .map((line) => line
      .replace(/^[=~_<>「」『』【】［］\[\]()（）]+|[=~_<>「」『』【】［］\[\]()（）]+$/g, '')
      .replace(/\s*([.．・･])\s*/g, '$1')
      .trim())
    .filter(Boolean);

  const ignored = /(読み込んで|配達|向かっています|住所|日本|〒|電話|建物|部屋|暗証|注文|受け渡し|マンション|アパート|ハイツ|ビル|号室|お客様|メモ|tel|phone)/i;
  const candidates = lines.filter((line) => {
    if (ignored.test(line) || /\d{2,}/.test(line)) return false;
    if (line.length < 1 || line.length > 28) return false;
    return /^[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}A-Za-z.．・･ー―‐\s-]+$/u.test(line);
  });

  const name = candidates[0] || '';
  return name
    .replace(/(?:様|さま)$/u, '')
    .replace(/\s+/g, ' ')
    .trim();
}

function parseOcrText(rawText) {
  const normalizedText = rawText.normalize('NFKC').replace(/\r/g, '');
  const lines = normalizedText.split('\n').map(cleanOcrLine).filter(Boolean);

  let name = valueAfterLabel(lines, [
    'お名前', '氏名', '名前', '宛名', '受取人', 'お届け先名', '届け先名', '顧客名', 'ご依頼主'
  ]);
  let building = valueAfterLabel(lines, [
    '建物名', 'マンション名', 'アパート名', 'ビル名', '施設名', '物件名'
  ]);
  let room = valueAfterLabel(lines, [
    '部屋番号', '部屋No\\.?', '室番号', 'Room', '号室'
  ]);

  const buildingWords = /(マンション|ハイツ|コーポ|メゾン|レジデンス|パレス|ビル|タワー|コート|プラザ|ハウス|アーバン|ロイヤル|グランド|シティ|荘|館)/i;
  if (!building) {
    building = lines.find((line) => buildingWords.test(line) && line.length <= 60) || '';
  }

  const roomMatch = normalizedText.match(/(?:部屋番号|部屋|室番号|room)\s*[:：#]?\s*([A-Za-z]?[\-－]?\d{2,6}(?:号室)?)/i);
  if (!room && roomMatch) room = roomMatch[1];
  if (!room) {
    const candidate = lines.find((line) => /^(?:[A-Za-z][\-－]?)?\d{2,6}(?:号室|室)$/.test(line));
    if (candidate) room = candidate;
  }

  if (!name) {
    const ignored = /(住所|電話|建物|部屋|暗証|注文|配達|マンション|ハイツ|ビル|号室|〒|tel|phone)/i;
    name = lines.find((line) => {
      if (ignored.test(line) || /\d{3,}/.test(line)) return false;
      return /^[\p{Script=Han}\p{Script=Hiragana}\p{Script=Katakana}A-Za-z・･ー\s]{2,24}(?:様)?$/u.test(line);
    }) || '';
  }

  name = name.replace(/(?:様|さま)$/u, '').trim();
  building = building
    .replace(/^(?:建物名|マンション名|アパート名|ビル名|施設名|物件名)\s*[:：]?\s*/i, '')
    .trim();
  room = room
    .replace(/^(?:部屋番号|部屋No\.?|室番号|Room)\s*[:：#]?\s*/i, '')
    .replace(/\s+/g, '')
    .trim();

  return { name, building, room, rawText: normalizedText };
}

async function runOcr() {
  if (!state.imageData) return;
  if (!window.Tesseract?.createWorker) {
    showToast('OCRライブラリを読み込めません。通信状態を確認してください');
    return;
  }

  const button = $('#ocrButton');
  const progressWrap = $('#ocrProgressWrap');
  const progressBar = $('#ocrProgressBar');
  const progressText = $('#ocrProgressText');
  setBusy(button, true, '読み取り中…');
  progressWrap.hidden = false;
  progressBar.style.width = '2%';
  progressText.textContent = '画像を最適化しています';

  let worker;
  let ocrPhase = 'full';
  try {
    const [preparedImage, preparedNameImage] = await Promise.all([
      prepareOcrImage(state.imageData),
      prepareDeliveryNameOcrImage(state.imageData)
    ]);
    worker = await Tesseract.createWorker(['jpn', 'eng'], 1, {
      logger(message) {
        const progress = Math.round((message.progress || 0) * 100);
        progressBar.style.width = `${Math.max(2, progress)}%`;
        const recognizingText = ocrPhase === 'name'
          ? `上部の太字名を読み取っています ${progress}%`
          : `建物名・部屋番号を読み取っています ${progress}%`;
        const statusMap = {
          'loading tesseract core': 'OCRエンジンを準備しています',
          'initializing tesseract': 'OCRを初期化しています',
          'loading language traineddata': '日本語データを読み込んでいます',
          'initializing api': '文字認識を準備しています',
          'recognizing text': recognizingText
        };
        progressText.textContent = statusMap[message.status] || recognizingText;
      }
    });
    await worker.setParameters({ preserve_interword_spaces: '1', user_defined_dpi: '300' });
    const result = await worker.recognize(preparedImage);
    const parsed = parseOcrText(result.data.text || '');

    ocrPhase = 'name';
    progressBar.style.width = '2%';
    progressText.textContent = '上部の太字名を切り出して読み取っています';
    await worker.reinitialize('jpn', 1);
    await worker.setParameters({
      preserve_interword_spaces: '1',
      user_defined_dpi: '300',
      tessedit_pageseg_mode: Tesseract.PSM.SINGLE_BLOCK
    });
    const nameResult = await worker.recognize(preparedNameImage);
    const deliveryName = extractDeliveryName(nameResult.data.text || '');
    if (deliveryName) parsed.name = deliveryName;

    state.ocrText = [
      parsed.rawText,
      deliveryName ? `上部の太字名: ${deliveryName}` : ''
    ].filter(Boolean).join('\n');

    if (parsed.name) $('#nameInput').value = parsed.name;
    if (parsed.building) $('#buildingInput').value = parsed.building;
    if (parsed.room) $('#roomInput').value = parsed.room;
    $('#ocrRawText').value = state.ocrText;
    $('#ocrDetails').hidden = false;
    progressBar.style.width = '100%';
    progressText.textContent = '読み取り完了';

    const detectedCount = [parsed.name, parsed.building, parsed.room].filter(Boolean).length;
    showToast(detectedCount ? `${detectedCount}項目を自動入力しました` : '項目を特定できませんでした。OCR全文をご確認ください');
  } catch (error) {
    console.error(error);
    showToast('OCR処理に失敗しました。手入力をご利用ください');
    progressText.textContent = '読み取りに失敗しました';
  } finally {
    if (worker) await worker.terminate().catch(() => {});
    setBusy(button, false);
    button.disabled = !state.imageData;
  }
}

function collectFormRecord() {
  const now = new Date().toISOString();
  const existing = state.records.find((record) => record.id === state.editingId);
  return {
    id: state.editingId || crypto.randomUUID(),
    name: $('#nameInput').value.trim(),
    building: $('#buildingInput').value.trim(),
    room: $('#roomInput').value.trim(),
    pin: $('#pinInput').value.trim(),
    memo: $('#memoInput').value.trim(),
    ocrText: state.ocrText || existing?.ocrText || '',
    imageData: $('#saveImageCheck').checked ? (state.imageData || existing?.imageData || '') : '',
    createdAt: existing?.createdAt || now,
    updatedAt: now
  };
}

async function handleRecordSave(event) {
  event.preventDefault();
  const record = collectFormRecord();
  if (![record.name, record.building, record.room, record.pin, record.memo].some(Boolean)) {
    showToast('少なくとも1項目を入力してください');
    return;
  }

  const button = $('#saveRecordButton');
  setBusy(button, true, '保存中…');
  try {
    await saveEnvelope(record);
    await loadRecords();
    const wasEdit = Boolean(state.editingId);
    resetForm();
    switchView('searchView');
    showToast(wasEdit ? '登録内容を更新しました' : '暗号化して保存しました');
  } catch (error) {
    console.error(error);
    showToast('保存に失敗しました');
  } finally {
    setBusy(button, false);
  }
}

function resetForm() {
  state.editingId = '';
  $('#editingId').value = '';
  $('#recordForm').reset();
  $('#formTitle').textContent = '登録内容';
  $('#saveRecordButton').textContent = '暗号化して保存';
  removeImage();
}

function editRecord(id) {
  const record = state.records.find((item) => item.id === id);
  if (!record) return;
  state.editingId = id;
  $('#editingId').value = id;
  $('#nameInput').value = record.name || '';
  $('#buildingInput').value = record.building || '';
  $('#roomInput').value = record.room || '';
  $('#pinInput').value = record.pin || '';
  $('#memoInput').value = record.memo || '';
  state.ocrText = record.ocrText || '';
  $('#ocrRawText').value = state.ocrText;
  $('#ocrDetails').hidden = !state.ocrText;
  state.imageData = record.imageData || '';
  if (state.imageData) {
    $('#imagePreview').src = state.imageData;
    $('#imagePreviewWrap').hidden = false;
    $('#ocrButton').disabled = false;
    $('#saveImageCheck').checked = true;
  } else {
    $('#imagePreviewWrap').hidden = true;
    $('#ocrButton').disabled = true;
    $('#saveImageCheck').checked = false;
  }
  $('#formTitle').textContent = '登録内容を編集';
  $('#saveRecordButton').textContent = '変更を保存';
  if ($('#recordDialog').open) $('#recordDialog').close();
  switchView('registerView');
}

async function deleteRecord(id) {
  const record = state.records.find((item) => item.id === id);
  if (!record) return;
  const label = record.name || record.building || record.room || 'この登録';
  if (!confirm(`「${label}」を削除しますか？\nこの操作は取り消せません。`)) return;
  try {
    await deleteEnvelope(id);
    if ($('#recordDialog').open) $('#recordDialog').close();
    await loadRecords();
    showToast('削除しました');
  } catch (error) {
    console.error(error);
    showToast('削除に失敗しました');
  }
}

function recordSearchText(record) {
  return normalizeSearch([
    record.name, record.building, record.room, record.pin,
    record.memo, record.ocrText
  ].filter(Boolean).join(' '));
}

function renderSearchResults() {
  const query = normalizeSearch($('#searchInput')?.value || '');
  const results = state.records.filter((record) => !query || recordSearchText(record).includes(query));
  const container = $('#searchResults');
  if (!container) return;

  container.innerHTML = results.map((record) => {
    const title = record.name || record.building || record.room || '名称未設定';
    const location = [record.building, record.room].filter(Boolean).join(' / ') || '建物・部屋番号未設定';
    const maskedPin = record.pin ? '●'.repeat(Math.min(Math.max(record.pin.length, 4), 10)) : '未設定';
    return `
      <article class="result-card">
        <h3>${escapeHtml(title)}</h3>
        <div class="result-meta">
          <span>${escapeHtml(location)}</span>
          <span>更新 ${escapeHtml(formatDate(record.updatedAt))}</span>
        </div>
        <div class="result-pin">暗証番号：${escapeHtml(maskedPin)}</div>
        <div class="result-actions">
          <button class="ghost-button" type="button" data-action="detail" data-id="${record.id}">詳細</button>
          <button class="secondary-button" type="button" data-action="edit" data-id="${record.id}">編集</button>
        </div>
      </article>`;
  }).join('');

  $('#emptyState').hidden = results.length > 0;
  if (!results.length) {
    $('#emptyState h3').textContent = query ? '一致する登録がありません' : '保存データはまだありません';
    $('#emptyState p').textContent = query ? '検索語を変えてお試しください。' : '「登録」から最初の情報を保存してください。';
  }
  $('#recordCountChip').textContent = query ? `${results.length}/${state.records.length}件` : `${state.records.length}件`;
}

function updateRecordCount() {
  const chip = $('#recordCountChip');
  if (chip) chip.textContent = `${state.records.length}件`;
}

function openRecordDialog(id) {
  const record = state.records.find((item) => item.id === id);
  if (!record) return;
  state.dialogId = id;
  $('#dialogTitle').textContent = record.name || record.building || '登録詳細';
  $('#dialogContent').innerHTML = `
    <dl class="detail-grid">
      ${detailItem('名前', record.name)}
      ${detailItem('建物名', record.building)}
      ${detailItem('部屋番号', record.room)}
      <div class="detail-item">
        <dt>暗証番号</dt>
        <dd class="pin-detail-row">
          <code id="dialogPin" data-pin="${escapeHtml(record.pin || '')}">${record.pin ? '●'.repeat(Math.min(Math.max(record.pin.length, 4), 10)) : '未設定'}</code>
          ${record.pin ? '<button id="revealDialogPin" class="icon-button" type="button">表示</button>' : ''}
        </dd>
      </div>
      ${detailItem('メモ', record.memo)}
      ${detailItem('登録日時', formatDate(record.createdAt))}
      ${detailItem('更新日時', formatDate(record.updatedAt))}
      ${record.imageData ? `<div class="detail-item"><dt>保存画像</dt><dd><img class="detail-image" src="${record.imageData}" alt="保存されたスクリーンショット"></dd></div>` : ''}
    </dl>`;
  $('#recordDialog').showModal();
}

function detailItem(label, value) {
  return `<div class="detail-item"><dt>${escapeHtml(label)}</dt><dd>${escapeHtml(value || '未設定')}</dd></div>`;
}

function toggleDialogPin() {
  const code = $('#dialogPin');
  const button = $('#revealDialogPin');
  if (!code || !button) return;
  const shown = button.textContent === '隠す';
  code.textContent = shown ? '●'.repeat(Math.min(Math.max(code.dataset.pin.length, 4), 10)) : code.dataset.pin;
  button.textContent = shown ? '表示' : '隠す';
}

async function updateBiometricSettings() {
  const status = $('#biometricStatus');
  const button = $('#biometricSettingsButton');
  if (!status || !button) return;

  const config = getBiometricConfig();
  if (config) {
    const protectionLabel = config.mode === 'prf' ? '認証情報由来の鍵で保護' : 'この端末専用の鍵で保護';
    status.textContent = `設定済み・${protectionLabel}・${formatDate(config.createdAt)}`;
    button.textContent = '解除する';
    button.disabled = false;
    return;
  }

  button.textContent = '設定する';
  if (!isWebAuthnAvailable()) {
    status.textContent = 'この環境では利用できません。HTTPSと対応ブラウザが必要です。';
    button.disabled = true;
    return;
  }

  const available = await platformAuthenticatorAvailable();
  status.textContent = available
    ? '指紋・顔・Windows Hello・端末PINなどで解除できます。'
    : 'この端末では生体・端末認証を確認できませんでした。';
  button.disabled = !available;
}

async function createBiometricCredential() {
  const credentialPromise = navigator.credentials.create({
    publicKey: {
      challenge: randomBytes(32),
      rp: {
        id: location.hostname,
        name: 'Entry Vault'
      },
      user: {
        id: randomBytes(32),
        name: `entry-vault-${Date.now()}`,
        displayName: 'Entry Vault'
      },
      pubKeyCredParams: [
        { type: 'public-key', alg: -7 },
        { type: 'public-key', alg: -257 }
      ],
      timeout: 120000,
      attestation: 'none',
      authenticatorSelection: {
        residentKey: 'preferred',
        requireResidentKey: false,
        userVerification: 'required'
      },
      hints: ['client-device']
    }
  });

  const credential = await credentialPromise;
  if (!credential) throw new Error('Credential creation was not completed');
  return credential;
}

async function buildDeviceModeBiometricConfig({ credentialId, transports, rawVaultKey }) {
  const wrappingKey = await crypto.subtle.generateKey(
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt', 'decrypt']
  );

  await saveBiometricWrappingKey(wrappingKey);
  const savedWrappingKey = await getBiometricWrappingKey(BIOMETRIC_KEY_RECORD_ID);
  if (!savedWrappingKey) throw new Error('Device wrapping key could not be stored');

  const wrappedKey = await encryptObject({
    marker: 'ENTRY_VAULT_BIOMETRIC_V2',
    rawKey: bytesToBase64(rawVaultKey)
  }, savedWrappingKey);

  return {
    version: BIOMETRIC_VERSION,
    mode: 'device',
    credentialId,
    transports,
    keyRecordId: BIOMETRIC_KEY_RECORD_ID,
    wrappedKey,
    createdAt: new Date().toISOString(),
    rpId: location.hostname
  };
}

async function enableBiometricUnlock() {
  const button = $('#biometricSettingsButton');
  setBusy(button, true, '設定中…');
  let stage = '開始';

  try {
    if (!state.cryptoKey) throw new Error('Vault is locked');
    if (!isWebAuthnAvailable()) throw new Error('WebAuthn is unavailable');

    const saltText = localStorage.getItem(KEY_SALT);
    if (!saltText) throw new Error('Vault salt is missing');

    /*
      WebAuthn登録はクリック直後に開始します。
      対応状況確認、PBKDF2、promptなどを先に実行すると、Android版Chromeで
      ユーザー操作権限が失効し、認証画面を開けないことがあります。
    */
    stage = '端末認証の登録';
    const credential = await createBiometricCredential();

    stage = 'マスターパスワードの確認';
    const masterPassword = prompt('端末認証を暗号鍵に関連付けるため、マスターパスワードを入力してください。');
    if (masterPassword === null) {
      const canceled = new Error('Master password entry was canceled');
      canceled.name = 'AbortError';
      throw canceled;
    }

    const exportableVaultKey = await deriveKey(
      masterPassword,
      base64ToBytes(saltText),
      true
    );

    try {
      await verifyVaultKey(exportableVaultKey);
    } catch (_) {
      throw new Error('Master password is incorrect');
    }

    stage = '暗号鍵の端末保存';
    const credentialId = bytesToBase64Url(new Uint8Array(credential.rawId));
    const transports = credential.response?.getTransports?.() || [];
    const rawVaultKey = new Uint8Array(await crypto.subtle.exportKey('raw', exportableVaultKey));

    try {
      await deleteBiometricWrappingKey().catch(() => {});
      const config = await buildDeviceModeBiometricConfig({
        credentialId,
        transports,
        rawVaultKey
      });
      localStorage.setItem(KEY_BIOMETRIC, JSON.stringify(config));
    } finally {
      rawVaultKey.fill(0);
    }

    configureAuthScreen();
    await updateBiometricSettings();
    showToast('生体・端末認証を設定しました');
  } catch (error) {
    console.error('Biometric setup failed', stage, error?.name, error?.message, error);

    localStorage.removeItem(KEY_BIOMETRIC);
    await deleteBiometricWrappingKey().catch(() => {});

    const errorName = error?.name || 'Error';
    const errorMessage = String(error?.message || '');
    let message;

    if (errorName === 'AbortError') {
      message = '認証設定を中止しました';
    } else if (errorMessage.includes('Master password')) {
      message = 'マスターパスワードが正しくありません';
    } else if (errorName === 'NotAllowedError') {
      message = '端末認証が完了しませんでした。指紋・顔・端末PINを完了してから再度お試しください';
    } else if (errorName === 'SecurityError') {
      message = 'このURLでは端末認証を登録できません';
    } else if (errorName === 'InvalidStateError') {
      message = '同じ認証情報が残っています。Chromeのパスキー設定からEntry Vaultを削除して再登録してください';
    } else if (errorName === 'NotSupportedError' || errorName === 'ConstraintError') {
      message = 'このChromeの認証方式では登録できません。ChromeとGoogle Playシステムを更新してください';
    } else if (errorName === 'DataCloneError' || errorMessage.includes('wrapping key')) {
      message = '端末内への暗号鍵保存に失敗しました。Chromeを更新して再度お試しください';
    } else {
      message = `生体・端末認証の設定に失敗しました（${stage}・${errorName}）`;
    }

    showToast(message);
  } finally {
    setBusy(button, false);
    await updateBiometricSettings();
  }
}

async function disableBiometricUnlock() {
  if (!confirm('この端末の生体・端末認証による解除を無効にしますか？')) return;
  const config = getBiometricConfig();
  localStorage.removeItem(KEY_BIOMETRIC);
  if (config?.keyRecordId) await deleteBiometricWrappingKey(config.keyRecordId).catch(() => {});
  configureAuthScreen();
  await updateBiometricSettings();
  showToast('生体・端末認証を解除しました');
}

async function toggleBiometricSetting() {
  if (getBiometricConfig()) await disableBiometricUnlock();
  else await enableBiometricUnlock();
}

async function updateStorageSummary() {
  const summary = $('#storageSummary');
  if (!summary) return;
  let storageText = `${state.records.length}件を端末内に保存`;
  if (navigator.storage?.estimate) {
    try {
      const estimate = await navigator.storage.estimate();
      const usageMb = ((estimate.usage || 0) / 1024 / 1024).toFixed(1);
      storageText += `・使用量 約${usageMb}MB`;
    } catch (_) {}
  }
  summary.textContent = storageText;
}

async function exportBackup() {
  const button = $('#exportButton');
  setBusy(button, true, '作成中…');
  try {
    const backup = {
      app: 'Entry Vault',
      version: 1,
      exportedAt: new Date().toISOString(),
      salt: localStorage.getItem(KEY_SALT),
      verifier: JSON.parse(localStorage.getItem(KEY_VERIFIER)),
      records: await getAllEnvelopes()
    };
    const blob = new Blob([JSON.stringify(backup, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = `entry-vault-backup-${new Date().toISOString().slice(0, 10)}.json`;
    link.click();
    URL.revokeObjectURL(url);
    showToast('暗号化バックアップを書き出しました');
  } catch (error) {
    console.error(error);
    showToast('バックアップ作成に失敗しました');
  } finally {
    setBusy(button, false);
  }
}

async function importBackup(file) {
  if (!file) return;
  try {
    const backup = JSON.parse(await file.text());
    if (backup.app !== 'Entry Vault' || backup.version !== 1 || !backup.salt || !backup.verifier || !Array.isArray(backup.records)) {
      throw new Error('Invalid backup');
    }
    if (!confirm('現在の保存内容を、選択したバックアップで置き換えますか？')) return;

    await clearAllEnvelopes();
    for (const envelope of backup.records) {
      await idbRequest('readwrite', (store) => store.put(envelope));
    }
    localStorage.setItem(KEY_SALT, backup.salt);
    localStorage.setItem(KEY_VERIFIER, JSON.stringify(backup.verifier));
    localStorage.removeItem(KEY_BIOMETRIC);
    await deleteBiometricWrappingKey().catch(() => {});
    showToast('復元しました。元のパスワードで再解除してください');
    setTimeout(lockApp, 500);
  } catch (error) {
    console.error(error);
    showToast('正しいバックアップファイルではありません');
  } finally {
    $('#importInput').value = '';
  }
}

async function deleteAllData() {
  if (!confirm('登録データをすべて削除しますか？')) return;
  if (!confirm('最終確認です。削除後はバックアップがない限り復元できません。')) return;
  try {
    await clearAllEnvelopes();
    state.records = [];
    renderSearchResults();
    updateStorageSummary();
    showToast('全登録データを削除しました');
  } catch (error) {
    console.error(error);
    showToast('削除に失敗しました');
  }
}

async function installApp() {
  if (!state.deferredInstallPrompt) {
    showToast('ブラウザのメニューから「ホーム画面に追加」を選択してください');
    return;
  }
  state.deferredInstallPrompt.prompt();
  await state.deferredInstallPrompt.userChoice;
  state.deferredInstallPrompt = null;
  $('#installButton').disabled = true;
}

function registerServiceWorker() {
  if ('serviceWorker' in navigator && location.protocol.startsWith('http')) {
    navigator.serviceWorker.register('sw.js').catch((error) => console.warn('SW registration failed', error));
  }
}

function bindEvents() {
  $('#authForm').addEventListener('submit', handleAuthSubmit);
  $('#biometricUnlockButton').addEventListener('click', () => handleBiometricUnlock());
  $('#quickLockButton').addEventListener('click', lockApp);
  $('#recordForm').addEventListener('submit', handleRecordSave);
  $('#resetFormButton').addEventListener('click', resetForm);
  $('#screenshotInput').addEventListener('change', (event) => handleScreenshot(event.target.files[0]));
  $('#removeImageButton').addEventListener('click', removeImage);
  $('#ocrButton').addEventListener('click', runOcr);
  $('#searchInput').addEventListener('input', renderSearchResults);
  $('#clearSearchButton').addEventListener('click', () => {
    $('#searchInput').value = '';
    renderSearchResults();
    $('#searchInput').focus();
  });

  $$('.nav-button').forEach((button) => button.addEventListener('click', () => switchView(button.dataset.view)));
  $$('[data-toggle-password]').forEach((button) => {
    button.addEventListener('click', () => {
      const input = document.getElementById(button.dataset.togglePassword);
      const shown = input.type === 'text';
      input.type = shown ? 'password' : 'text';
      button.textContent = shown ? '表示' : '隠す';
    });
  });

  $('#searchResults').addEventListener('click', (event) => {
    const button = event.target.closest('button[data-action]');
    if (!button) return;
    if (button.dataset.action === 'detail') openRecordDialog(button.dataset.id);
    if (button.dataset.action === 'edit') editRecord(button.dataset.id);
  });

  $('#closeDialogButton').addEventListener('click', () => $('#recordDialog').close());
  $('#recordDialog').addEventListener('click', (event) => {
    if (event.target === $('#recordDialog')) $('#recordDialog').close();
    if (event.target.closest('#revealDialogPin')) toggleDialogPin();
  });
  $('#dialogEditButton').addEventListener('click', () => editRecord(state.dialogId));
  $('#dialogDeleteButton').addEventListener('click', () => deleteRecord(state.dialogId));

  $('#refreshStorageButton').addEventListener('click', updateStorageSummary);
  $('#biometricSettingsButton').addEventListener('click', toggleBiometricSetting);
  $('#exportButton').addEventListener('click', exportBackup);
  $('#importInput').addEventListener('change', (event) => importBackup(event.target.files[0]));
  $('#deleteAllButton').addEventListener('click', deleteAllData);
  $('#installButton').addEventListener('click', installApp);

  ['pointerdown', 'keydown', 'input', 'touchstart'].forEach((eventName) => {
    document.addEventListener(eventName, resetAutoLock, { passive: true });
  });

  window.addEventListener('beforeinstallprompt', (event) => {
    event.preventDefault();
    state.deferredInstallPrompt = event;
    $('#installButton').disabled = false;
  });
}

async function init() {
  bindEvents();
  configureAuthScreen();
  registerServiceWorker();
  if (!window.isSecureContext) {
    console.warn('Web Crypto/PWA features require HTTPS or localhost.');
  }
  maybeAutoBiometricUnlock();
}

document.addEventListener('DOMContentLoaded', init);
