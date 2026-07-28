import sys
import yaml

special_benchmarks = ["extra_args"]

# Instruction counts are deterministic under canbench, so a regression over this
# many percent is a real change rather than measurement noise.
DEFAULT_THRESHOLD = 10.0

if (len(sys.argv) < 3):
  print("Usage: python diff.py <current.yml> <base.yml> [threshold_percent]")
  sys.exit(2)

threshold = float(sys.argv[3]) if len(sys.argv) > 3 else DEFAULT_THRESHOLD

# (benchmark, metric, percent) for every instruction count over the threshold.
regressions = []

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

def percent(current, base):
  if base == 0:
    return 0.0
  return (current - base) / base * 100

def display_diff(current, base):
  d = percent(current, base)
  if d < 0:
    return f"{current:_} ($\\textcolor{{green}}{{{d:.2f}\\\\%}}$)"
  elif d > 0:
    return f"{current:_} ($\\textcolor{{red}}{{{d:.2f}\\\\%}}$)"
  else:
    return f"{current:_}"

def display_gated(name, metric, current, base):
  """Same as display_diff, but records anything over the threshold.

  Only instruction counts are gated. Memory is reported but not gated:
  heap_increase is page-granular, so a one-page move on a small footprint is a
  large percentage with no real meaning.
  """
  d = percent(current, base)
  if d > threshold:
    regressions.append((name, metric, d))
  return display_diff(current, base)

def print_table(data, base):
  print("| Name | Max Mem (Kb) | Encode | Decode |")
  print("|:--- |:--- |:--- |:---|")
  for name in data.keys():
    if name not in special_benchmarks:
      mem, encode, decode = get_numbers(name, data)
      if base.get(name) is not None:
        base_mem, base_encode, base_decode = get_numbers(name, base)
        mem = display_diff(mem, base_mem)
        encode = display_gated(name, "encode", encode, base_encode)
        decode = display_gated(name, "decode", decode, base_decode)
      else:
        name = "**" + name + " (new)**"
        mem = f"{mem:_}"
        encode = f"{encode:_}"
        decode = f"{decode:_}"
      print(f"| {name} | {mem} | {encode} | {decode} |")

  print()
  parse = data["nns"]["scopes"]["0. Parsing"]["instructions"]
  base_parse = base["nns"]["scopes"]["0. Parsing"]["instructions"]
  print(f"* Parser cost: {display_gated('nns', 'parsing', parse, base_parse)}")
  extra = data["extra_args"]["total"]["instructions"]
  base_extra = base["extra_args"]["total"]["instructions"]
  print(f"* Extra args: {display_gated('extra_args', 'total', extra, base_extra)}")

current = load_yaml(sys.argv[1])
base = load_yaml(sys.argv[2])
print_table(current, base)

if regressions:
  print()
  print("> [!CAUTION]")
  print(f"> Instruction counts regressed by more than {threshold:g}%:")
  for name, metric, d in regressions:
    print(f"> - `{name}` {metric}: **+{d:.2f}%**")
  sys.exit(1)
