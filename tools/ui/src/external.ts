interface ExternalConfig {
  candid?: string;
}

type MessageListener = (message: any) => void;

const hasExternalConfig = new URLSearchParams(window.location.search).has(
  "external-config"
);

const messagePrefix = "CandidUI";

// Starting with a hard-coded origin list for security
const allowedExternalOrigins = [
  "localhost:4943", // Local
  "http://ryjl3-tyaaa-aaaaa-aaaba-cai.localhost:4943", // Motoko Playground (local)
  "https://m7sm4-2iaaa-aaaab-qabra-cai.raw.icp0.io", // Motoko Playground (mainnet)
  "https://m7sm4-2iaaa-aaaab-qabra-cai.icp0.io", // Motoko Playground (certified)
  "https://m7sm4-2iaaa-aaaab-qabra-cai.raw.ic0.app", // Motoko Playground (legacy, mainnet)
  "https://m7sm4-2iaaa-aaaab-qabra-cai.ic0.app", // Motoko Playground (legacy, certified)
  "https://play.motoko.org", // Motoko Playground (custom domain)
];

const messageListeners: MessageListener[] = [];

export function addMessageListener(listener: MessageListener) {
  messageListeners.push(listener);
}

export function removeMessageListener(listener: MessageListener) {
  const index = messageListeners.indexOf(listener);
  if (index !== -1) {
    messageListeners.splice(index, 1);
  }
}

window.addEventListener("message", ({ origin, source, data }) => {
  if (typeof data === "string" && data.startsWith(messagePrefix)) {
    if (allowedExternalOrigins.includes(origin)) {
      const message = JSON.parse(data.substring(messagePrefix.length));
      console.log("Candid UI received message:", message);
      try {
        if (
          message?.acknowledge !== undefined &&
          !(source instanceof MessagePort)
        ) {
          source?.postMessage?.(
            `${messagePrefix}${JSON.stringify({
              type: "acknowledge",
              acknowledge: message.acknowledge,
            })}`,
            origin as any
          );
        }
      } catch (err) {
        console.error("Unable to send message acknowledgement:", err);
      }
      messageListeners.forEach((listener) => listener(message));
    } else {
      console.warn(
        "Candid UI received message from unexpected origin:",
        origin
      );
    }
  }
});

/**
 * Use this global promise to safely access `external-config` data provided through `postMessage()`.
 */
export const EXTERNAL_CONFIG_PROMISE: Promise<ExternalConfig> = new Promise(
  (resolve) => {
    if (!hasExternalConfig) {
      return resolve({});
    }
    let resolved = false;

    // Listen for "config" messages
    addMessageListener((message) => {
      if (message?.type === "config") {
        resolved = true;
        return resolve({ ...message.config });
      }
    });

    setTimeout(() => {
      if (!resolved) {
        console.error("External config timeout");
        resolve({});
      }
    }, 3000);
  }
);
