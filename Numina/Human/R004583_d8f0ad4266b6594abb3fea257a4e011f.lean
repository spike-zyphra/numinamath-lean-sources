import Mathlib

theorem number_theory_286577 :
    Set.ncard {n : ℕ | 0 < n ∧ IsSquare (7 * n + 1) ∧ 3 * n + 1 < 2008} = 18 := by
  convert Set.ncard_coe_Finset {n ∈ Finset.Ioo 0 669 | IsSquare (7 * n + 1)}
  . ext x
    simp
    have : 3 * x + 1 < 2008 ↔ x < 669 := by omega
    tauto
  . native_decide
