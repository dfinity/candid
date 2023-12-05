import { Principal } from "@dfinity/principal"
import { authClient } from "../candid"
import { refresh_actor } from "../index"
import { dfinityLogo, copyIcon } from "./icons"

export async function renderAuth() {
  const is_logged = await authClient?.isAuthenticated();
  is_logged ? insertLogout() : insertLoginForm();
}

function is_valid_url(url: string): boolean {
  let obj;
  try {
    obj = new URL(url);
  } catch (_) {
    return false;
  }
  return obj.protocol === "http:" || obj.protocol === "https:";
}

function insertLoginForm() {
  const auth = document.getElementById("authentication")!;
  const buttonLogin = document.createElement("button");
  buttonLogin.className = "btn btn-auth";
  buttonLogin.innerHTML = `${dfinityLogo} Login`;
  auth.appendChild(buttonLogin);

  try {
    const params = new URLSearchParams(window.location.search);
    const is_mainnet = window.location.hostname.endsWith("icp0.io") || window.location.hostname.endsWith("ic0.app");
    let provider = params.get("ii");
    if (is_mainnet && !provider) {
      provider = "https://identity.internetcomputer.org";
    }
    if (!provider) {
      throw new Error("Please provide internet identity url in ii parameter");
    }
    if (provider && !is_valid_url(provider)) {
      throw new Error("Please provide a valid internet identity url in ii parameter");
    }
    const origin = params.get("origin");
    if (origin && !is_valid_url(origin)) {
      throw new Error("Please provide a valid derivationOrigin url in origin parameter");
    }
    const cid = Principal.fromText(params.get("id")!);

    buttonLogin.addEventListener("click", async () => {
      let config: any = {
        identityProvider: provider,
        onSuccess: async () => {
          refresh_actor(cid);
          insertLogout();
        },
        onError: (err: any) => console.error(err),
      };
      if (origin) {
        config = {...config, derivationOrigin: origin};
      }
      await authClient?.login(config);
    });
  } catch (err) {
    buttonLogin.disabled = true;
    buttonLogin.title = (err as any).toString();
  }
}

function insertLogout() {
  const auth = document.getElementById("authentication");
  auth!.innerHTML = "";

  CopyId();
  LogoutButton();
}

function LogoutButton() {
  const auth = document.getElementById("authentication");

  const buttonLogout = document.createElement("button");
  buttonLogout.className = "btn random";
  buttonLogout.style.margin = "10px";
  buttonLogout.innerText = "Logout";

  buttonLogout.addEventListener("click", async () => {
    await logout();
  })

  auth!.appendChild(buttonLogout);
}

function CopyId() {
  if (!authClient) {
    return;
  }

  const auth = document.getElementById("authentication");

  const copyText = document.createElement("span");

  const id = authClient.getIdentity().getPrincipal().toString();
  const idShort = id.slice(0, 5) + "..." + id.slice(-5);
  copyText.innerText = idShort;

  const copyButton = document.createElement("button");
  copyButton.id = "copyButton";
  copyButton.style.cursor = "pointer";
  copyButton.innerHTML = `${copyIcon}`;

  copyButton.addEventListener("click", function () {
    navigator.clipboard.writeText(id).catch((err) => {
      console.error(err);
    })
    copyText.innerText = "Copied!";
    setTimeout(() => {
      copyText.innerText = idShort;
    }, 2000)
  })

  auth?.appendChild(copyButton);
  auth?.appendChild(copyText);
}

async function logout() {
  authClient?.logout();
  window.location.reload();
}
