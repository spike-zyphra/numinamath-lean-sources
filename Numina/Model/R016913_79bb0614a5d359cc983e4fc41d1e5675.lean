import Mathlib

theorem number_theory_208968 : ∑ n in (Finset.Icc 1000 9999).filter (fun n => ∀ d ∈ Nat.digits 10 n, d ≠ 0 ∧ d ≠ 9), n ≡ 0 [ZMOD 101] := by
  native_decide