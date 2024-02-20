import yaml

def load_yaml(input_file):
  # Load the YAML data
  with open(input_file, 'r') as f:
    data = yaml.safe_load(f)["benches"]

  print("| Name | Max Mem | Encode | Decode |")
  print("| --- | --- | --- | --- |")
  for name in data.keys():
    scope = data[name]["scopes"]
    mem = data[name]["total"]["heap_increase"] * 64 / 1024
    encode = scope["1. Encoding"]["instructions"]
    decode = scope["2. Decoding"]["instructions"]
    print(f"| {name} | {mem:.2f} | {encode:_} | {decode:_} |")

  print()
  print(f"Parser cost: {data['nns']['scopes']['0. Parsing']['instructions']:_}")

input_file = "canbench_results.yml"
load_yaml(input_file)
