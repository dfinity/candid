import { EXTERNAL_CONFIG_PROMISE } from './external';
import { Actor, HttpAgent, ActorSubclass, CanisterStatus, getManagementCanister } from '@dfinity/agent';
import {
  IDL, InputBox, renderInput, renderValue
} from '@dfinity/candid';
import {Principal} from '@dfinity/principal'
import './candid.css';
import { AuthClient } from "@dfinity/auth-client";

declare var flamegraph: any;
declare var d3: any;

const names: Record<number,string> = {};

function isKnownMainnet(agent: HttpAgent) {
  // @ts-ignore
  const hostname = agent.host.hostname;
  return hostname.endsWith('.icp0.io') || hostname.endsWith('.ic0.app');
}

export let authClient: AuthClient | undefined;

const agent = HttpAgent.createSync();
if (!isKnownMainnet(agent)) {
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
  const base64Source = (await EXTERNAL_CONFIG_PROMISE)?.candid || window.history.state?.candid || maybeDid;
  if (base64Source) {
    js = await didToJs(window.atob(base64Source));
    if (!js) {
      console.warn('Nothing returned from didjs for base64 input:', base64Source);
    }
  }
  if (!js) {
    js = await getDidJsFromMetadata(canisterId);
    if (!js) {
      try {
        js = await getDidJsFromTmpHack(canisterId);
      } catch(err) {
        if (/no query method/.test(err as any)) {
          console.warn(err);
          js = undefined;
        } else {
          throw(err);
        }
      }
    }
  }
  if (!js) {
    throw new Error('Cannot fetch candid file');
  }
  const dataUri = 'data:text/javascript;charset=utf-8,' + encodeURIComponent(js);
  const candid: any = await eval('import("' + dataUri + '")');

  authClient = authClient ?? (await AuthClient.create({
    idleOptions: {
      disableIdle: true,
      disableDefaultIdleCallback: true,
    },
  }))
  if (await authClient.isAuthenticated()) {
    agent.replaceIdentity(authClient.getIdentity());
    console.log("Authenticated with Internet Identity Principal")
    console.log(authClient.getIdentity().getPrincipal().toString())
  }

  return Actor.createActor(candid.idlFactory, { agent, canisterId });
}

export function getProfilerActor(canisterId: Principal): ActorSubclass {
  const profiler_interface: IDL.InterfaceFactory = ({ IDL }) => IDL.Service({
    __get_profiling: IDL.Func([IDL.Int32], [IDL.Vec(IDL.Tuple(IDL.Int32, IDL.Int64)), IDL.Opt(IDL.Int32)], ['query']),
    __get_cycles: IDL.Func([], [IDL.Int64], ['query']),
  });
  return Actor.createActor(profiler_interface, { agent, canisterId });
}
function uint8ArrayToDisplay(array: Uint8Array | number[]) {
  const uint8Array = new Uint8Array(array);
  try {
    return new TextDecoder().decode(uint8Array);
  } catch (e) {
    return Array.from(uint8Array)
      .map(byte => byte.toString(16).padStart(2, '0'))
      .join(' ');
  }
}
function timestampToString(nanoseconds: bigint) {
  const milliseconds = Number(nanoseconds / 1000000n);
  const date = new Date(milliseconds);
  const timeString = date.toLocaleTimeString(undefined, {
    hour: '2-digit',
    minute: '2-digit',
    second: '2-digit',
    hour12: false,
  });
  const ms = date.getMilliseconds().toString().padStart(3, '0');
  return `${timeString}.${ms}`;
}

let last_log_idx: bigint = -1n;
export async function getCanisterLogs(canisterId: Principal, logger: any) {
  try {
    const actor = getManagementCanister({ agent });
    const logs = await actor.fetch_canister_logs({ canister_id: canisterId });
    let array = logs.canister_log_records;
    const idx = array.findIndex((e) => e.idx > last_log_idx);
    if (idx > 0) {
      array = array.slice(idx);
    }
    if (array.length > 0) {
      last_log_idx = array[array.length - 1].idx;
      const display = array.map((e) => {
        const stamp = timestampToString(e.timestamp_nanos);
        const content = uint8ArrayToDisplay(e.content);
        return `[${stamp}] ${content}`;
      });
      const content = display.join("<br>");
      logger(content);
    }
  } catch(err) {
    console.warn(err);
  }
}

function postToPlayground(id: Principal) {
  const message = {
    caller: id.toText(),
  };
  (window.parent || window.opener)?.postMessage(`CandidUI${JSON.stringify(message)}`, '*');
}

export async function getCycles(canisterId: Principal): Promise<bigint|undefined> {
  try {
    const actor = getProfilerActor(canisterId);
    const cycles = await actor.__get_cycles() as bigint;
    return cycles;
  } catch(err) {
    return undefined;
  }
}

export async function getNames(canisterId: Principal) {
  try {
    const paths : CanisterStatus.Path[] = [{
      kind: 'metadata',
      path: 'name',
      key: 'name',
      decodeStrategy: 'raw',
    }];
    const status = await CanisterStatus.request({ agent, canisterId, paths });
    const blob = status.get('name') as ArrayBuffer;
    const decoded = IDL.decode([IDL.Vec(IDL.Tuple(IDL.Nat16, IDL.Text))], blob)[0] as Array<[number,string]>;
    decoded.forEach(([id, name]) => names[id] = name);
  } catch(err) {
    return undefined;
  }
}

async function getDidJsFromPostMessage(canisterId: Principal): Promise<undefined | string> {
  return new Promise((resolve,reject)=>{})
}

async function getDidJsFromMetadata(canisterId: Principal): Promise<undefined | string> {
  const status = await CanisterStatus.request({ agent, canisterId, paths: ['candid'] });
  const did = status.get('candid') as string | null;
  if (did) {
    return didToJs(did);
  } else {
    return undefined;
  }
}

export async function getProfiling(canisterId: Principal): Promise<Array<[number, bigint]>|undefined> {
  try {
    const actor = getProfilerActor(canisterId);
    let info: Array<[number, bigint]> = [];
    let idx = 0;
    let cnt = 0;
    while (cnt < 50) {
      const [res, next] = await actor.__get_profiling(idx) as [Array<[number, bigint]>, [number]|[]];
      info = info.concat(res);
      if (next.length === 1) {
        idx = next[0];
        cnt++;
      } else {
        break;
      }
    }
    return info;
  } catch(err) {
    console.log(err);
    return undefined;
  }
}
function decodeProfiling(input: Array<[number, bigint]>) {
  //console.log(input);
  if (!input || input.length == 0) {
    return undefined;
  }
  const stack: Array<[number, bigint, any[]]> = [[0,BigInt(0),[]]];
  let prev_id = undefined;
  let i = 1;
  for (const [id, cycles] of input) {
    if (id >= 0) {
      stack.push([id, cycles, []]);
    } else {
      const pair = stack.pop();
      if (!pair) {
        console.log(i);
        throw new Error("cannot pop empty stack");
      }
      if (pair[0] !== -id) {
        throw new Error(`Exiting func ${-pair[0]}, but expect to exit func ${id}`);
      }
      const name = names[pair[0]] || `func_${pair[0]}`;
      const value: number = Number(cycles - pair[1]);
      let result = pair[2];
      const node = { name, value };
      if (typeof prev_id === "number" && prev_id < 0) {
        result = [{ ...node, children: result }];
      } else {
        result.push(node);
      }
      stack[stack.length-1][2].push(...result);
    }
    prev_id = id;
    i++;
  }
  if (stack.length !== 1) {
    console.log(stack);
    throw new Error("End of input, but stack is not empty");
  }
  if (stack[0][2].length === 1) {
    return stack[0][2][0];
  } else {
    const total_cycles = Number(input[input.length - 1][1] - input[0][1]);
    return { children: stack[0][2], name: "Total", value: total_cycles };
  }
}
async function renderFlameGraph(profiler: any) {
  const profiling = decodeProfiling(await profiler());
  //console.log(profiling);
  if (typeof profiling !== 'undefined') {
    let div = document.createElement('div');
    div.id = 'chart';
    log(div);
    const chart = flamegraph().selfValue(false).sort(false).width(400);
    const tip = flamegraph.tooltip.defaultFlamegraphTooltip().text((d:any) => `${d.data.name}: ${d.data.value} instrs`);
    chart.tooltip(tip);
    d3.select("#chart").datum(profiling).call(chart);
    div.id = 'old-chart';
  }
}

async function getDidJsFromTmpHack(canisterId: Principal): Promise<undefined | string> {
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
  if (JSON.stringify(js) === JSON.stringify([])) {
    return undefined;
  }
  return js[0];
}

function is_query(func: IDL.FuncClass): boolean {
  return func.annotations.includes('query') || func.annotations.includes('composite_query');
}

export function render(id: Principal, canister: ActorSubclass, profiling: bigint|undefined) {
  document.getElementById('canisterId')!.innerText = `${id}`;
  getCanisterLogs(id, log);
  let profiler;
  if (typeof profiling !== 'undefined') {
    log(`Wasm instructions executed ${profiling} instrs.`);
    profiler = async () => { return await getProfiling(id) };
    renderFlameGraph(profiler);
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
  if (is_query(idlFunc)) {
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

    const tStart = Date.now();
    const result = await canister[name](...args);
    const duration = (Date.now() - tStart) / 1000;
    right.innerText = `(${duration}s)`;
    return result;
  }

  const containers: HTMLDivElement[] = [];
  function callAndRender(args: any[]) {
    (async () => {
      resultDiv.classList.remove('error');
      const showArgs = encodeStr(IDL.FuncClass.argsToString(idlFunc.argTypes, args));
      log(decodeSpace(`› ${name}${showArgs}`));
      const callResult = await call(args) as any;
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
      if (!is_query(idlFunc)) {
        const id = Actor.canisterIdOf(canister);
        await getCanisterLogs(id, log);
        postToPlayground(id);
        if (profiler) {
          await renderFlameGraph(profiler);
        }
      }
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
      if (!is_query(idlFunc)) {
        const id = Actor.canisterIdOf(canister);
        getCanisterLogs(id, log);
        postToPlayground(id);
        if (profiler) {
          log(`Error occured, flamegraph can be incomplete`);
          renderFlameGraph(profiler);
        }
      }
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

