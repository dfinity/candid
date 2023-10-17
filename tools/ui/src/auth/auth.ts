import { Principal } from "@dfinity/principal"
import { authClient } from "../candid"
import { refresh_actor } from "../index"
import { dfinity_logo, copy_icon } from "./icons"
import { identityProvider } from "./identityProvider"

export async function renderAuth() {
  ;(await authClient?.isAuthenticated()) ? insertLogout() : insertLoginForm()
}

type DerivationOriginOptions = {
  canisterId: Principal
  domain: string
  raw: boolean
}

function insertLoginForm() {
  const params = new URLSearchParams(window.location.search)
  const cid = params.get("id")
  if (!cid) {
    throw new Error("No canister ID available for authentication")
  } else {
    const auth = document.getElementById("authentication")

    const buttonLogin = document.createElement("button")
    buttonLogin.className = "btn"
    buttonLogin.style.margin = "10px"
    buttonLogin.innerHTML = `${dfinity_logo} Login with Internet Identity`

    const canisterId = Principal.fromText(cid)

    buttonLogin.addEventListener("click", async () => {
      const options: DerivationOriginOptions = {
        canisterId,
        domain: (document.getElementById("domain") as HTMLInputElement).checked
          ? "icp0.io"
          : "ic0.app",
        raw: (document.getElementById("raw") as HTMLInputElement).checked,
      }
      await login(options)
    })

    const { raw, raw_label, domain, domain_label } = domainForm()

    auth!.innerHTML = ""
    auth!.appendChild(raw)
    auth!.appendChild(raw_label)
    auth!.appendChild(domain)
    auth!.appendChild(domain_label)
    auth!.appendChild(buttonLogin)
  }
}

function domainForm() {
  const raw = document.createElement("input")
  raw.id = "raw"
  raw.type = "checkbox"
  raw.checked = true

  const raw_label = document.createElement("label")
  raw_label.innerText = "raw"
  raw_label.style.marginRight = "10px"

  const domain = document.createElement("input")
  domain.id = "domain"
  domain.type = "checkbox"
  domain.checked = true

  const domain_label = document.createElement("label")
  domain_label.innerText = "icp0.io"

  return { raw, raw_label, domain, domain_label }
}

function insertLogout() {
  const auth = document.getElementById("authentication")
  auth!.innerHTML = ""

  CopyId()
  LogoutButton()
}

function LogoutButton() {
  const auth = document.getElementById("authentication")

  const buttonLogout = document.createElement("button")
  buttonLogout.className = "btn random"
  buttonLogout.style.margin = "10px"
  buttonLogout.innerText = "Logout"

  buttonLogout.addEventListener("click", async () => {
    await logout()
  })

  auth!.appendChild(buttonLogout)
}

function CopyId() {
  if (!authClient) {
    return
  }

  const auth = document.getElementById("authentication")

  const copyText = document.createElement("span")

  const id = authClient.getIdentity().getPrincipal().toString()
  const idShort = id.slice(0, 5) + "..." + id.slice(-5)
  copyText.innerText = idShort

  const copyButton = document.createElement("button")
  copyButton.id = "copyButton"
  copyButton.style.cursor = "pointer"
  copyButton.innerHTML = `${copy_icon}`

  copyButton.addEventListener("click", function () {
    navigator.clipboard.writeText(id).catch((err) => {
      console.error(err)
    })
    copyText.innerText = "Copied!"
    setTimeout(() => {
      copyText.innerText = idShort
    }, 2000)
  })

  auth?.appendChild(copyButton)
  auth?.appendChild(copyText)
}

async function login(options: DerivationOriginOptions) {
  authClient?.login({
    identityProvider,
    derivationOrigin: derivationOrigin(options),
    onSuccess: async () => {
      refresh_actor(options.canisterId)
      insertLogout()
    },
    onError: (err) => console.error(err),
  })
}

async function logout() {
  authClient?.logout()
  window.location.reload()
}

function derivationOrigin(options: DerivationOriginOptions): string {
  if (options.domain !== "icp0.io" && options.domain !== "ic0.app") {
    throw new Error("Invalid domain")
  }

  return options.raw
    ? "https://" + options.canisterId.toString() + ".raw." + options.domain
    : "https://" + options.canisterId.toString() + "." + options.domain
}
