import { fetchActor, render } from './candid';
import { Principal } from '@dfinity/agent';

const params = new URLSearchParams(window.location.search);
const cid = params.get('id');
if (!cid) {
  const app = document.getElementById('app');
  app!.innerHTML = 'id not found';
} else {
  (async () => {
    const canisterId = Principal.fromText(cid);
    const didjs = Principal.fromText('rrkah-fqaaa-aaaaa-aaaaq-cai');
    const actor = await fetchActor(didjs, canisterId);
    const div = document.createElement('div');
    document.body.appendChild(div);
    render(cid, actor);
  })();
}
