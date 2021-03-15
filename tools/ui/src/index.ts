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
    const actor = await fetchActor(canisterId);
    render(cid, actor);
  })();
}
