import { Principal } from "@dfinity/principal"
import { authClient } from "./candid"
import { refresh_actor } from "./index"
import { dfinity_logo, copy_icon } from "./icons"

export async function renderAuth(canisterId: Principal) {
  ;(await authClient?.isAuthenticated())
    ? insertLogout()
    : insertLoginButton(canisterId)
}

function insertLoginButton(canisterId: Principal) {
  const auth = document.getElementById("authentication")

  const buttonLogin = document.createElement("button")
  buttonLogin.className = "btn"
  buttonLogin.innerHTML = `${dfinity_logo} Login with Internet Identity`

  buttonLogin.addEventListener("click", async () => {
    await login(canisterId)
  })

  auth!.innerHTML = ""
  auth!.appendChild(buttonLogin)
}

function insertLogout() {
  const auth = document.getElementById("authentication")
  auth!.innerHTML = ""

  insertCopyId()
  insertLogoutButton()
}

function insertLogoutButton() {
  const auth = document.getElementById("authentication")

  const buttonLogout = document.createElement("button")
  buttonLogout.className = "btn random"
  buttonLogout.innerText = "Logout"

  buttonLogout.addEventListener("click", async () => {
    await logout()
  })

  auth!.appendChild(buttonLogout)
}

function insertCopyId() {
  if (!authClient) {
    return
  }

  const auth = document.getElementById("authentication")

  const copyText = document.createElement("span")

  const id = authClient.getIdentity().getPrincipal().toString()
  const idShort = id.slice(0, 5) + "..." + id.slice(-5)
  copyText.innerText = idShort

  const copyButton = document.createElement("button")
  copyButton.innerHTML = `${copy_icon}`

  copyButton.addEventListener("click", function () {
    navigator.clipboard.writeText(id).catch((err) => {
      console.error(err)
    })
  })

  auth?.appendChild(copyText)
  auth?.appendChild(copyButton)
}

async function login(canisterId: Principal) {
  const identityProvider = "https://identity.ic0.app"
  const derivationOrigin = "https://" + canisterId.toString() + ".raw.icp0.io"

  authClient?.login({
    identityProvider,
    derivationOrigin,
    onSuccess: async () => {
      refresh_actor(canisterId)
      await insertLogout()
    },
    onError: (err) => console.error(err),
  })
}

async function logout() {
  authClient?.logout()
  window.location.reload()
}
