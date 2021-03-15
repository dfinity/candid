import { fetchActor, render } from './candid';
import { Principal } from '@dfinity/agent';

async function main() {
  const params = new URLSearchParams(window.location.search);
  const cid = params.get('id');
  if (!cid) {
    throw new Error('Provide parameter id in the URL as the target canister id');
  } else {
    const canisterId = Principal.fromText(cid);
    const actor = await fetchActor(canisterId);
    render(canisterId, actor);
  }
}

main().catch(err => {
  const div = document.createElement('div');
  div.innerText = 'An error happened in Candid canister:';
  const pre = document.createElement('pre');
  pre.innerHTML = err.stack;
  div.appendChild(pre);
  const app = document.getElementById('app');
  app!.innerHTML = '';
  app!.appendChild(div);
  throw err;
});
