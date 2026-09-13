From Stdlib Require Import Extraction
  ExtrOcamlBasic ExtrOcamlNativeString
  ExtrOcamlZBigInt ExtrOcamlNatBigInt.
From Examples Require Import ThresholdIns.
Extraction Blacklist String List Nat Ascii Byte Decimal.
Set Extraction Output Directory ".".
Separate Extraction ThresholdIns.
