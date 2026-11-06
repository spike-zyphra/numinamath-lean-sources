import Mathlib
theorem number_theory_608896 : (∑ i in Finset.range 2011, 2 ^ ((i + 1) * (i + 2) / 2)) ≡ 1 [MOD 7]:= by
  native_decide