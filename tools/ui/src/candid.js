import { Actor, IDL, Principal, UI } from '@dfinity/agent';
import didjs from 'ic:canisters/didjs';

export async function fetchActor(canisterId) {
  const common_interface = ({ IDL }) => IDL.Service({
    __get_candid_interface_tmp_hack: IDL.Func([], [IDL.Text], ['query']),
  });
  const actor = Actor.createActor(common_interface, { canisterId });
  const candid_source = await actor.__get_candid_interface_tmp_hack();
  const candid = await didToJs(candid_source);
  return Actor.createActor(candid.default, { canisterId });
}

export async function didToJs(source) {
  const js = await didjs.did_to_js(source);
  if (js === []) {
    return undefined;
  }
  const dataUri = 'data:text/javascript;charset=utf-8,' + encodeURIComponent(js[0]);
  const candid = await eval('import("' + dataUri + '")');
  return candid;
}

export function render(dom, id, canister) {
  dom.innerHTML = `
<div>This service has the following methods:
<ul id="methods"></ul></div>
<div class="console" id="candid_console"></div>
`;
  for (const [name, func] of Actor.interfaceOf(canister)._fields) {
    renderMethod(canister, name, func);
  }
}

function renderMethod(canister, name, idlFunc) {
  const item = document.createElement('li');

  const sig = document.createElement('div');
  sig.className = 'signature';
  sig.innerHTML = `${name}: ${idlFunc.display()}`;
  item.appendChild(sig);

  const inputs = [];
  idlFunc.argTypes.forEach((arg, i) => {
    const inputbox = UI.renderInput(arg);
    inputs.push(inputbox);
    inputbox.render(item);
  });

  const button = document.createElement('button');
  button.className = 'btn';
  if (idlFunc.annotations.includes('query')) {
    button.innerText = 'Query';
  } else {
    button.innerText = 'Call';
  }
  item.appendChild(button);

  const random = document.createElement('button');
  random.className = 'btn';
  random.innerText = 'Lucky';
  item.appendChild(random);

  const resultDiv = document.createElement('div');
  resultDiv.className = 'result';
  const left = document.createElement('span');
  left.className = 'left';
  const right = document.createElement('span');
  right.className = 'right';
  resultDiv.appendChild(left);
  resultDiv.appendChild(right);
  item.appendChild(resultDiv);

  const list = document.getElementById('methods');
  list.append(item);

  async function call(args) {
    left.className = 'left';
    left.innerText = 'Waiting...';
    right.innerText = '';
    resultDiv.style.display = 'block';

    const tStart = Date.now();
    const result = await canister[name](...args);
    const duration = (Date.now() - tStart) / 1000;
    right.innerText = `(${duration}s)`;
    return result;
  }

  function callAndRender(args) {
    (async () => {
      const callResult = await call(args);
      let result;
      if (idlFunc.retTypes.length === 0) {
        result = [];
      } else if (idlFunc.retTypes.length === 1) {
        result = [callResult];
      } else {
        result = callResult;
      }
      left.innerHTML = '';

      const containers = [];
      const textContainer = document.createElement('div');
      containers.push(textContainer);
      left.appendChild(textContainer);
      const text = encodeStr(IDL.FuncClass.argsToString(idlFunc.retTypes, result));
      textContainer.innerHTML = text;
      const showArgs = encodeStr(IDL.FuncClass.argsToString(idlFunc.argTypes, args));
      log(`› ${name}${showArgs}`);
      log(text);

      const uiContainer = document.createElement('div');
      containers.push(uiContainer);
      uiContainer.style.display = 'none';
      left.appendChild(uiContainer);
      idlFunc.retTypes.forEach((arg, ind) => {
        const box = UI.renderInput(arg);
        box.render(uiContainer);
        UI.renderValue(arg, box, result[ind]);
      });

      const jsonContainer = document.createElement('div');
      containers.push(jsonContainer);
      jsonContainer.style.display = 'none';
      left.appendChild(jsonContainer);
      jsonContainer.innerText = JSON.stringify(callResult);

      let i = 0;
      left.addEventListener('click', () => {
        containers[i].style.display = 'none';
        i = (i + 1) % 3;
        containers[i].style.display = 'block';
      });
    })().catch(err => {
      left.className += ' error';
      left.innerText = err.message;
      throw err;
    });
  }

  random.addEventListener('click', () => {
    const args = inputs.map(arg => arg.parse({ random: true }));
    const isReject = inputs.some(arg => arg.isRejected());
    if (isReject) {
      return;
    }
    callAndRender(args);
  });

  button.addEventListener('click', () => {
    const args = inputs.map(arg => arg.parse());
    const isReject = inputs.some(arg => arg.isRejected());
    if (isReject) {
      return;
    }
    callAndRender(args);
  });
}

function encodeStr(str) {
  const escapeChars = {
    ' ': '&nbsp;',
    '<': '&lt;',
    '>': '&gt;',
    '\n': '<br>',
  };
  const regex = new RegExp('[ <>\n]', 'g');
  return str.replace(regex, m => {
    return escapeChars[m];
  });
}

function log(content) {
  const consoleEl = document.getElementById('candid_console');
  const line = document.createElement('div');
  line.className = 'console-line';
  if (content instanceof Element) {
    line.appendChild(content);
  } else {
    line.innerHTML = content;
  }
  consoleEl.appendChild(line);
}
