import Mathlib

theorem algebra_181352 (a : Fin 6 → ℕ) (h₀ : ∑ i, a i = 129)
    (h₁ : a 0 - 6 = a 1 - 11) (h₂ : a 1 - 11 = a 2 - 8) (h₃ : a 2 - 8 = a 3 - 10)
    (h₄ : a 3 - 10 = a 4 - 7) (h₅ : a 4 - 7 = a 5 - 9) :
    a = ![19, 24, 21, 23, 20, 22] := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₀
  have eq1 : a 0 + a 1 + a 2 + a 3 + a 4 + a 5 = 129 := by
    linarith
  have h6 : a 0 = 19 := by
    omega
  have h7 : a 1 = 24 := by
    omega
  have h8 : a 2 = 21 := by
    omega
  have h9 : a 3 = 23 := by
    omega
  have h10 : a 4 = 20 := by
    omega
  have h11 : a 5 = 22 := by
    omega
  funext i
  fin_cases i <;> simp [h6, h7, h8, h9, h10, h11]
  all_goals try { tauto }