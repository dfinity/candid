import { fetchActor, render } from './candid';
import { Principal } from '@dfinity/agent';

async function main() {
  const params = new URLSearchParams(window.location.search);
  const cid = params.get('id');
  if (!cid) {
    throw new Error('Provide parameter id in the URL as the target canister id');
  } else {
    document.title = `Canister ${cid}`;
    const canisterId = Principal.fromText(cid);
    const actor = await fetchActor(canisterId);
    render(canisterId, actor);
    const app = document.getElementById('app');
    const progress = document.getElementById('progress');
    progress!.remove();
    app!.style.display = 'block';
  }
}

main().catch(err => {
  const div = document.createElement('div');
  div.innerText = 'An error happened in Candid canister:';
  const pre = document.createElement('pre');
  pre.innerHTML = err.stack;
  div.appendChild(pre);
  const progress = document.getElementById('progress');
  progress!.remove();
  document.body.appendChild(div);
  throw err;
});
