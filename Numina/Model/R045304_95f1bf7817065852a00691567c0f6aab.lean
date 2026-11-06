import Mathlib

theorem algebra_109820 (a : ℝ) (f : ℝ → ℝ)
    (h₀ : ∀ x, f x = x ^ 3 - a * x ^ 2 + (a ^ 2 - 2) * x + 1)
    (h₁ : ∃ m, 0 < m ∧ f m ≤ 0) :
    a ≤ 1 := by
  rcases h₁ with ⟨m, hm_pos, hfm⟩
  have h_eq : f m = m ^ 3 - a * m ^ 2 + (a ^ 2 - 2) * m + 1 := by
    apply h₀
  rw [h_eq] at hfm
  nlinarith [sq_nonneg (a - 1), sq_nonneg (m - 1), sq_nonneg (a - m), sq_nonneg ((a * m) - m), sq_nonneg ((a) + m), sq_nonneg (a - 2 * m), sq_nonneg (a ^ 2 - 2), sq_nonneg (m ^ 2 - 1), sq_nonneg (m * (a - 1)), mul_pos hm_pos (show 0 < m from hm_pos)]