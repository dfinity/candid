import { fetchActor, render } from './candid';
import { Principal } from '@dfinity/agent';

async function main() {
  const params = new URLSearchParams(window.location.search);
  const cid = params.get('id');
  if (!cid) {
    document.body.innerHTML = `<div id="main-content">
<label>Provide a canister ID: </label>
<input id="id" type="text">
<button id="btn" class="btn">Go</button>
</div>
`;
    const id = document.getElementById('id')!;
    const btn = document.getElementById('btn')!;
    btn.addEventListener('click', () => {
      params.append('id', (id as any).value);
      window.location.href = `?${params}`;
    });
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
