let loading;

export function loadWasm() {
  if (!globalThis.crossOriginIsolated) {
    return Promise.reject(new Error("ホストは localhost または HTTPS で画面を開いてください。"));
  }
  loading ??= new Promise((resolve, reject) => {
    window.Module = {
      noInitialRun: true,
      onRuntimeInitialized() {
        const module = window.Module;
        if (module.ccall("fab_web_init", "number") === 1) resolve(module);
        else reject(new Error("Leanの初期化に失敗しました。"));
      },
      onAbort: reject,
    };
    const script = document.createElement("script");
    script.src = "/wasm/fab.js";
    script.onerror = () => reject(new Error("WASMの読み込みに失敗しました。"));
    document.head.append(script);
  });
  return loading;
}

export function sampleIndex(bound) {
  const value = new Uint32Array(1);
  const limit = 2 ** 32 - (2 ** 32 % bound);
  do {
    crypto.getRandomValues(value);
  } while (value[0] >= limit);
  return value[0] % bound;
}
