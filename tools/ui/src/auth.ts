import { Principal } from "@dfinity/principal"
import { authClient } from "./candid";

export async function renderAuth(canisterId: Principal) {
  ;(await authClient?.isAuthenticated())
    ? insertLogoutButton()
    : insertLoginButton(canisterId)
}

function insertLoginButton(canisterId: Principal) {
  const auth = document.getElementById("authentication")

  const buttonLogin = document.createElement("button")
  buttonLogin.className = "btn"
  buttonLogin.innerText = "Login with Internet Identity"

  buttonLogin.addEventListener("click", async () => {
    await login(canisterId)
  })

  auth!.innerHTML = '';
  auth!.appendChild(buttonLogin)
}

function insertLogoutButton() {
  const auth = document.getElementById("authentication")

  const buttonLogout = document.createElement("button")
  buttonLogout.className = "btn random"
  buttonLogout.innerText = "Logout"

  buttonLogout.addEventListener("click", async () => {
    await logout()
  })

  auth!.innerHTML = '';
  auth!.appendChild(buttonLogout)
}

async function login(canisterId: Principal) {
  const identityProvider = "https://identity.ic0.app"
  const derivationOrigin = "https://" + canisterId.toString() + ".raw.icp0.io"

  authClient?.login({
    identityProvider,
    derivationOrigin,
    onSuccess: async() => {
        window.location.reload()
        console.log(authClient?.getIdentity())
    },
    onError: (err) => console.error(err),
  })
}

async function logout() {
  authClient?.logout()
  window.location.reload()
}
