import Mathlib

theorem algebra_153752 (f : ℝ → ℝ) (hf : f = fun x => x^10 - x^9 + x^4 - x + 1) :
    ¬∃ x : ℝ, f x = 0 := by 
  intro h
  rcases h with ⟨x, hx⟩
  rw [hf] at hx
  simp at hx
  nlinarith [sq_nonneg (x^5 - x^4 / 2), sq_nonneg (x^4 - 1 / 2), sq_nonneg (x^3 + 1 / 2), sq_nonneg (x^2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x^5 - x^2), sq_nonneg (x^4 - x), sq_nonneg (x^3 - x^2), sq_nonneg (x^2 - x), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^5 - x), sq_nonneg (x^4 - 1), sq_nonneg (x^3 - 1), sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1)]