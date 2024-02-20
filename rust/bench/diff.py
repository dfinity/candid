import yaml

special_benchmarks = ["extra_args"]

def load_yaml(input_file):
  # Load the YAML data
  with open(input_file, 'r') as f:
    data = yaml.safe_load(f)["benches"]

  print("| Name | Max Mem(Kb) | Encode | Decode |")
  print("| --- | --- | --- | --- |")
  for name in data.keys():
    if name not in special_benchmarks:
      scope = data[name]["scopes"]
      mem = data[name]["total"]["heap_increase"] * 64
      encode = scope["1. Encoding"]["instructions"]
      decode = scope["2. Decoding"]["instructions"]
      print(f"| {name} | {mem:_} | {encode:_} | {decode:_} |")

  print()
  print(f"* Parser cost: {data['nns']['scopes']['0. Parsing']['instructions']:_}")
  print(f"* Extra args: {data['extra_args']['total']['instructions']:_}")

input_file = "canbench_results.yml"
load_yaml(input_file)
