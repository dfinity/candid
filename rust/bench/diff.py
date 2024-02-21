import sys
import yaml

special_benchmarks = ["extra_args"]

if (len(sys.argv) < 3):
  print("Usage: python diff.py <current.yml> <base.yml>")
  sys.exit(1)

def load_yaml(input_file):
  # Load the YAML data
  with open(input_file, 'r') as f:
    data = yaml.safe_load(f)["benches"]
  return data

def get_numbers(name, data):
  scope = data[name]["scopes"]
  mem = data[name]["total"]["heap_increase"] * 64
  encode = scope["1. Encoding"]["instructions"]
  decode = scope["2. Decoding"]["instructions"]
  return (mem, encode, decode)

def display_diff(current, base):
  if base == 0:
    d = 0
  else:
    d = (current - base) / base * 100
  if d < 0:
    return f"{current:_} ($\\textcolor{{green}}{{{d:.2f}\\\\%}}$)"
  elif d > 0:
    return f"{current:_} ($\\textcolor{{red}}{{{d:.2f}\\\\%}}$)"
  else:
    return f"{current:_}"

def print_table(data, base):
  print("| Name | Max Mem (Kb) | Encode | Decode |")
  print("|:--- |:--- |:--- |:---|")
  for name in data.keys():
    if name not in special_benchmarks:
      mem, encode, decode = get_numbers(name, data)
      if base.get(name) is not None:
        base_mem, base_encode, base_decode = get_numbers(name, base)
        mem = display_diff(mem, base_mem)
        encode = display_diff(encode, base_encode)
        decode = display_diff(decode, base_decode)
      else:
        name = "**" + name + " (new)**"
        mem = f"{mem:_}"
        encode = f"{encode:_}"
        decode = f"{decode:_}"
      print(f"| {name} | {mem} | {encode} | {decode} |")

  print()
  parse = data["nns"]["scopes"]["0. Parsing"]["instructions"]
  base_parse = base["nns"]["scopes"]["0. Parsing"]["instructions"]
  print(f"* Parser cost: {display_diff(parse, base_parse)}")
  extra = data["extra_args"]["total"]["instructions"]
  base_extra = base["extra_args"]["total"]["instructions"]
  print(f"* Extra args: {display_diff(extra, base_extra)}")

current = load_yaml(sys.argv[1])
base = load_yaml(sys.argv[2])
print_table(current, base)
