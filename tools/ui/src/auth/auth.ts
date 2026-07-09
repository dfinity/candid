import { Principal } from "@icp-sdk/core/principal"
import { authClient, createAuthClient } from "../candid"
import { refresh_actor } from "../index"
import { dfinityLogo, copyIcon } from "./icons"

export async function renderAuth() {
  const is_logged = authClient?.isAuthenticated() ?? false;
  is_logged ? await insertLogout() : insertLoginForm();
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

async function check_alternative_origin(): Promise<boolean> {
  try {
    const url = window.location.origin;
    const response = await fetch(`${url}/.well-known/ii-alternative-origins`);
    const data = await response.json();
    if (data.hasProperty("alternativeOrigins") && Array.isArray(data["alternativeOrigins"])) {
      return data["alternativeOrigins"].some((origin: string) => origin === url);
    }
    return false;
  } catch (_) {
    return false;
  }
}

async function insertLoginForm() {
  const auth = document.getElementById("authentication")!;
  const buttonLogin = document.createElement("button");
  buttonLogin.className = "btn btn-auth";
  buttonLogin.innerHTML = `${dfinityLogo} Login`;
  auth.appendChild(buttonLogin);

  try {
    const params = new URLSearchParams(window.location.search);
    const mainnet_domains = ["icp0.io", "ic0.app", "icp.net"];
    const mainnet_domain = mainnet_domains.find((domain) => window.location.hostname.endsWith(domain));
    const is_mainnet = mainnet_domain !== undefined;
    let provider = params.get("ii");
    if (is_mainnet && !provider) {
      provider = "https://identity.internetcomputer.org";
    }
    if (!provider) {
      console.warn("If you want to use Internet Identity, please provide a URL to your local Internet Identity service using the `ii` query parameter");
      return;
    }
    if (provider && !is_valid_url(provider)) {
      throw new Error("Please provide a valid URL to your local Internet Identity service using the `ii` query parameter");
    }
    const cid = Principal.fromText(params.get("id")!);
    let origin = params.get("origin");
    if (!origin && is_mainnet && await check_alternative_origin()) {
      origin = `https://${cid.toText()}.${mainnet_domain}`;
    }
    if (origin) {
      if (!is_valid_url(origin)) {
        throw new Error("Please provide a valid URL in the `origin` query parameter");
      }
      console.warn("`derivationOrigin` is enabled. Remember to disable alternative origins in the production canister.");
    }

    buttonLogin.addEventListener("click", async () => {
      try {
        const client = createAuthClient({
          identityProvider: provider!,
          ...(origin ? { derivationOrigin: origin } : {}),
        });
        await client.signIn();
        refresh_actor(cid);
        await insertLogout();
      } catch (err) {
        console.error(err);
      }
    });
  } catch (err) {
    console.error(err);
    buttonLogin.disabled = true;
    buttonLogin.classList.add("disabled");
    buttonLogin.title = (err as any).toString();
  }
}

async function insertLogout() {
  const auth = document.getElementById("authentication");
  auth!.innerHTML = "";

  await CopyId();
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

async function CopyId() {
  if (!authClient) {
    return;
  }

  const auth = document.getElementById("authentication");

  const copyText = document.createElement("span");

  const identity = await authClient.getIdentity();
  const id = identity.getPrincipal().toString();
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
  await authClient?.signOut();
  window.location.reload();
}
