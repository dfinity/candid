export const IDL = `
  type StoreNumberInput = record {
    number : nat64;
  };

  type CustomType = record {
    custom_field : nat64;
    options: CustomVariant;
  };

  type CustomVariant = variant {
    A : nat64;
    B : text;
  };

  service : {
    store_number : (input : StoreNumberInput) -> ();
    get_number : () -> (nat64) query;
    set_complex_type : (input : CustomType) -> ();
  };
`;

export const IDL_SERVICE_METHODS = [
  "store_number",
  "get_number",
  "set_complex_type",
];
