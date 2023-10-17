import { fetchActor, render, getCycles, getNames } from "./candid";
import { renderAuth } from "./auth/auth";
import { Principal } from "@dfinity/principal";
import { ActorSubclass } from "@dfinity/agent";

let actor: ActorSubclass | undefined;

async function main() {
  const params = new URLSearchParams(window.location.search);
  const cid = params.get("id");
  if (!cid) {
    document.body.innerHTML = `<div id="main-content">
    <label>Provide a canister ID: </label>
    <input id="id" type="text"><br>
    <label>Choose a did file (optional) </label>
    <input id="did" type="file" accept=".did"><br>
    <button id="btn" class="btn">Go</button>
    </div>
    `;
    const id = (document.getElementById("id") as HTMLInputElement)!;
    const did = (document.getElementById("did")! as HTMLInputElement)!;
    const btn = document.getElementById("btn")!;
    btn.addEventListener("click", () => {
      params.set("id", id.value);
      if (did.files!.length > 0) {
        const reader = new FileReader();
        reader.addEventListener("load", () => {
          const encoded = reader.result as string;
          const candid = encoded.substr(encoded.indexOf(",") + 1);
          // update URL with Candid data and refresh
          window.history.pushState({}, "", window.location.search);
          window.history.pushState({ candid }, "", `?${params}`);
          window.location.reload();
        });
        reader.readAsDataURL(did.files![0]);
      } else {
        window.location.href = `?${params}`;
      }
    });
  } else {
    document.title = `Canister ${cid}`;
    const canisterId = Principal.fromText(cid);
    const profiling = await getCycles(canisterId);
    actor = await fetchActor(canisterId);
    await renderAuth();
    const names = await getNames(canisterId);
    render(canisterId, actor, profiling);
    const app = document.getElementById("app");
    const progress = document.getElementById("progress");
    progress!.remove();
    app!.style.display = "block";
  }
}

main().catch((err) => {
  const div = document.createElement("div");
  div.innerText = "An error happened in Candid canister:";
  const pre = document.createElement("pre");
  pre.innerHTML = err.stack;
  div.appendChild(pre);
  const progress = document.getElementById("progress");
  progress!.remove();
  document.body.appendChild(div);
  throw err;
});

// Reload when going back after uploading custom Candid data
window.addEventListener("popstate", (event) => {
  if (event.state) {
    window.location.reload();
  }
});

export async function refresh_actor(canisterId: Principal) {
  actor = await fetchActor(canisterId);
};
