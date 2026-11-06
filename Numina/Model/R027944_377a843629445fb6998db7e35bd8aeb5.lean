import Mathlib
open Real

theorem algebra_94587
  (c : ℝ)
  (h : ∃ k, k^2 - 8 * k + c = 0 ∧ (∀ x, k^2 - 8 * k + c ≤ x^2 - 8 * x + c)) :
  c = 16 :=
by
  rcases h with ⟨k, hk1, hk2⟩
  have h4' := hk2 4
  have h1 : (k - 4) ^ 2 ≤ 0 := by
    nlinarith
  have hk2' : k = 4 := by
    nlinarith [sq_nonneg (k - 4)]
  rw [hk2'] at hk1
  nlinarith