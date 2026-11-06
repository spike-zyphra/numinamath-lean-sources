import Mathlib
theorem algebra_605313 {a : Fin 5 → ℝ} (ha : ∀ k : ℕ, 1 ≤ k ∧ k ≤ 5 →
    a 0 / (k ^ 2 + 1) + a 1 / (k ^ 2 + 2) + a 2 / (k ^ 2 + 3) +
    a 3 / (k ^ 2 + 4) + a 4 / (k ^ 2 + 5) = 1 / k ^ 2) :
    a 0 / 37 + a 1 / 38 + a 2 / 39 + a 3 / 40 + a 4 / 41 = 187465 / 6744582 := by
  have eq1 := ha 1 (by norm_num)
  have eq2 := ha 2 (by norm_num)
  have eq3 := ha 3 (by norm_num)
  have eq4 := ha 4 (by norm_num)
  have eq5 := ha 5 (by norm_num)
  norm_num at eq1 eq2 eq3 eq4 eq5
  linarith