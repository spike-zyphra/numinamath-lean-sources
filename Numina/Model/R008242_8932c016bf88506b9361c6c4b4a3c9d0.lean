import Mathlib

theorem number_theory_15408 :
    ∑ x in (Finset.Icc 1 20).filter (fun x => 13 * (3 * x - 2) ≡ 26 [ZMOD 8]), x = 36 := by
  native_decide