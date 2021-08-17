import { Actor, HttpAgent, ActorSubclass } from '@dfinity/agent';
import {
  IDL, InputBox, renderInput, renderValue
} from '@dfinity/candid';
import {Principal} from '@dfinity/principal'
import './candid.css';

function is_local(agent: HttpAgent) {
  // @ts-ignore
  const hostname = agent._host.hostname;
  return hostname === '127.0.0.1' || hostname.endsWith('localhost');
}

const agent = new HttpAgent();
if (is_local(agent)) {
  agent.fetchRootKey();
}

function getCanisterId(): Principal {
  // Check the query params.
  const maybeCanisterId = new URLSearchParams(window.location.search).get(
    "canisterId"
  );
  if (maybeCanisterId) {
    return Principal.fromText(maybeCanisterId);
  }

  // Return the first canister ID when resolving from the right hand side.
  const domain = window.location.hostname.split(".").reverse();
  for (const subdomain of domain) {
    try {
      if (subdomain.length >= 25) {
        // The following throws if it can't decode or the checksum is invalid.
        return Principal.fromText(subdomain);
      }
    } catch (_) {}
  }

  throw new Error("Could not find the canister ID.");
}

export async function fetchActor(canisterId: Principal): Promise<ActorSubclass> {
  let js;
  const maybeDid = new URLSearchParams(window.location.search).get(
    "did"
  );
  if (maybeDid) {
    const source = window.atob(maybeDid);
    js = await didToJs(source);
  } else {
    try {
      js = await getRemoteDidJs(canisterId);
    } catch(err) {
      if (/no query method/.test(err)) {
        js = await getLocalDidJs(canisterId);
      } else {
        throw(err);
      }
    }
  }
  if (!js) {
    throw new Error('Cannot fetch candid file');
  }
  const dataUri = 'data:text/javascript;charset=utf-8,' + encodeURIComponent(js);
  const candid: any = await eval('import("' + dataUri + '")');
  return Actor.createActor(candid.idlFactory, { agent, canisterId });
}

export async function getCycles(canisterId: Principal): Promise<[bigint,bigint]|undefined> {
  try {
    const profiling_interface: IDL.InterfaceFactory = ({ IDL }) => IDL.Service({
      __get_cycles: IDL.Func([], [IDL.Int64, IDL.Int64], ['query']),
    });
    const actor: ActorSubclass = Actor.createActor(profiling_interface, { agent, canisterId });
    const cycles = await actor.__get_cycles() as [bigint, bigint];
    return cycles;
  } catch(err) {
    return undefined;
  }
}

async function getLocalDidJs(canisterId: Principal): Promise<undefined | string> {
  const origin = window.location.origin;
  const url = `${origin}/_/candid?canisterId=${canisterId.toText()}&format=js`;
  const response = await fetch(url);
  if (!response.ok) {
    return undefined;
  }
  return response.text();
}

async function getRemoteDidJs(canisterId: Principal): Promise<undefined | string> {
  const common_interface: IDL.InterfaceFactory = ({ IDL }) => IDL.Service({
    __get_candid_interface_tmp_hack: IDL.Func([], [IDL.Text], ['query']),
  });
  const actor: ActorSubclass = Actor.createActor(common_interface, { agent, canisterId });
  const candid_source = await actor.__get_candid_interface_tmp_hack() as string;
  return didToJs(candid_source);
}

async function didToJs(candid_source: string): Promise<undefined | string> {
  // call didjs canister
  const didjs_id = getCanisterId();
  const didjs_interface: IDL.InterfaceFactory = ({ IDL }) => IDL.Service({
    did_to_js: IDL.Func([IDL.Text], [IDL.Opt(IDL.Text)], ['query']),
  });
  const didjs: ActorSubclass = Actor.createActor(didjs_interface, { agent, canisterId: didjs_id });
  const js: any = await didjs.did_to_js(candid_source);
  if (js === []) {
    return undefined;
  }
  return js[0];  
}

export function render(id: Principal, canister: ActorSubclass, profiling: [bigint,bigint]|undefined) {
  document.getElementById('canisterId')!.innerText = `${id}`;
  let profiler;
  if (profiling) {
    log(`Wasm instructions executed ${profiling[0]} (GC ${profiling[1]} instrs)`);
    profiler = async () => { return await getCycles(id) };
  }
  const sortedMethods = Actor.interfaceOf(canister)._fields.sort(([a], [b]) => (a > b ? 1 : -1));
  for (const [name, func] of sortedMethods) {
    renderMethod(canister, name, func, profiler);
  }
}

function renderMethod(canister: ActorSubclass, name: string, idlFunc: IDL.FuncClass, profiler: any) {
  const item = document.createElement('li');
  item.id = name;

  const sig = document.createElement('div');
  sig.className = 'signature';
  sig.innerHTML = `<b>${name}</b>: ${idlFunc.display()}`;
  item.appendChild(sig);

  const methodListItem = document.createElement('li');
  const methodLink = document.createElement('a');
  methodLink.innerText = name;
  methodLink.href = `#${name}`;
  methodListItem.appendChild(methodLink);
  document.getElementById('methods-list')!.appendChild(methodListItem);

  const inputContainer = document.createElement('div');
  inputContainer.className = 'input-container';
  item.appendChild(inputContainer);

  const inputs: InputBox[] = [];
  idlFunc.argTypes.forEach((arg, i) => {
    const inputbox = renderInput(arg);
    inputs.push(inputbox);
    inputbox.render(inputContainer);
  });

  const buttonContainer = document.createElement('div');
  buttonContainer.className = 'button-container';

  const buttonQuery = document.createElement('button');
  buttonQuery.className = 'btn';
  if (idlFunc.annotations.includes('query')) {
    buttonQuery.innerText = 'Query';
  } else {
    buttonQuery.innerText = 'Call';
  }
  buttonContainer.appendChild(buttonQuery);

  const buttonRandom = document.createElement('button');
  buttonRandom.className = 'btn random';
  buttonRandom.innerText = 'Random';
  buttonContainer.appendChild(buttonRandom);
  item.appendChild(buttonContainer);

  const resultDiv = document.createElement('div');
  resultDiv.className = 'result';
  const left = document.createElement('div');
  left.className = 'left';
  const right = document.createElement('div');
  right.className = 'right';

  const resultButtons = document.createElement('span');
  resultButtons.className = 'result-buttons';
  const buttonText = document.createElement('button');
  buttonText.className = 'btn text-btn active';
  buttonText.innerText = 'Text';
  const buttonUI = document.createElement('button');
  buttonUI.className = 'btn ui-btn';
  buttonUI.innerText = 'UI';
  const buttonJSON = document.createElement('button');
  buttonJSON.className = 'btn json-btn';
  buttonJSON.innerText = 'JSON';
  const buttonsArray = [buttonText, buttonUI, buttonJSON];

  resultDiv.appendChild(resultButtons);
  resultDiv.appendChild(left);
  resultDiv.appendChild(right);
  item.appendChild(resultDiv);

  const list = document.getElementById('methods')!;
  list.append(item);

  async function call(args: any[]) {
    left.className = 'left';
    left.innerText = 'Waiting...';
    right.innerText = '';
    resultDiv.style.display = 'flex';

    const before_instrs = profiler ? (await profiler() as [bigint, bigint]) : null;
    const tStart = Date.now();
    const result = await canister[name](...args);
    const duration = (Date.now() - tStart) / 1000;
    const instr_counter = profiler ? ((await profiler() as [bigint, bigint]).map((now, i) => now-before_instrs![i])) : null;
    right.innerText = `(${duration}s)`;
    return [result, instr_counter];
  }

  const containers: HTMLDivElement[] = [];
  function callAndRender(args: any[]) {
    (async () => {
      resultDiv.classList.remove('error');
      const [callResult, instr_counter] = await call(args) as [any, [bigint, bigint]];
      let result: any;
      if (idlFunc.retTypes.length === 0) {
        result = [];
      } else if (idlFunc.retTypes.length === 1) {
        result = [callResult];
      } else {
        result = callResult;
      }
      left.innerHTML = '';

      let activeDisplayType = '';
      buttonsArray.forEach(button => {
        if (button.classList.contains('active')) {
          activeDisplayType = button.classList.value.replace(/btn (.*)-btn.*/g, '$1');
        }
      });
      function setContainerVisibility(displayType: string) {
        if (displayType === activeDisplayType) {
          return 'flex';
        }
        return 'none';
      }
      function decodeSpace(str: string) {
        return str.replace(/&nbsp;/g, ' ');
      }

      const textContainer = document.createElement('div');
      textContainer.className = 'text-result';
      containers.push(textContainer);
      textContainer.style.display = setContainerVisibility('text');
      left.appendChild(textContainer);
      const text = encodeStr(IDL.FuncClass.argsToString(idlFunc.retTypes, result));
      textContainer.innerHTML = decodeSpace(text);
      const showArgs = encodeStr(IDL.FuncClass.argsToString(idlFunc.argTypes, args));
      const showInstr = instr_counter && instr_counter[0]?`(${instr_counter[0]} instrs, GC ${instr_counter[1]} instrs)`:"";
      log(decodeSpace(`› ${name}${showArgs} ` + showInstr));
      log(decodeSpace(text));

      const uiContainer = document.createElement('div');
      uiContainer.className = 'ui-result';
      containers.push(uiContainer);
      uiContainer.style.display = setContainerVisibility('ui');
      left.appendChild(uiContainer);
      idlFunc.retTypes.forEach((arg, ind) => {
        const box = renderInput(arg);
        box.render(uiContainer);
        renderValue(arg, box, result[ind]);
      });

      const jsonContainer = document.createElement('div');
      jsonContainer.className = 'json-result';
      containers.push(jsonContainer);
      jsonContainer.style.display = setContainerVisibility('json');
      left.appendChild(jsonContainer);
      jsonContainer.innerText = JSON.stringify(callResult, (k,v) => typeof v === 'bigint'?v.toString():v);
    })().catch(err => {
      resultDiv.classList.add('error');
      left.innerText = err.message;
      throw err;
    });
  }

  function selectResultDisplay(event: MouseEvent) {
    const target = event.target as HTMLButtonElement;
    const displayType = target.classList.value.replace(/btn (.*)-btn.*/g, '$1');
    buttonsArray.forEach(button => button.classList.remove('active'));
    containers.forEach(container => (container.style.display = 'none'));
    target.classList.add('active');
    (left.querySelector(`.${displayType}-result`) as HTMLDivElement).style.display = 'flex';
  }
  buttonsArray.forEach(button => {
    button.addEventListener('click', selectResultDisplay);
    resultButtons.appendChild(button);
  });

  buttonRandom.addEventListener('click', () => {
    const args = inputs.map(arg => arg.parse({ random: true }));
    const isReject = inputs.some(arg => arg.isRejected());
    if (isReject) {
      return;
    }
    callAndRender(args);
  });

  buttonQuery.addEventListener('click', () => {
    const args = inputs.map(arg => arg.parse());
    const isReject = inputs.some(arg => arg.isRejected());
    if (isReject) {
      return;
    }
    callAndRender(args);
  });
}

function encodeStr(str: string) {
  const escapeChars: Record<string, string> = {
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

function log(content: Element | string) {
  const outputEl = document.getElementById('output-list')!;
  const line = document.createElement('div');
  line.className = 'output-line';
  if (content instanceof Element) {
    line.appendChild(content);
  } else {
    line.innerHTML = content;
  }

  outputEl.appendChild(line);
  line.scrollIntoView();
}

