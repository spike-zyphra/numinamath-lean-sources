import Mathlib

theorem number_theory_67069 :
    ∏ i ∈ Finset.range 1000, (2 * i + 2) ≡ ∏ i ∈ Finset.range 1000, (2 * i + 1) [MOD 2001] := by 
  native_decide