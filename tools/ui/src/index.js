import { fetchActor, render } from './candid';
import './candid.css';

const params = new URLSearchParams(window.location.search);
const canisterId = params.get('id');
if (!canisterId) {
  document.write('id not found');
} else {
  (async () => {
    const actor = await fetchActor(canisterId);
    const div = document.createElement('div');
    document.body.appendChild(div);
    render(div, canisterId, actor);
  })();
}
