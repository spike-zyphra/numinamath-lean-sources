import Mathlib

theorem algebra_151566 (f : ℝ → ℝ) (hf : f = fun x => x^6 - x^5 + x^4 - x^3 + x^2 - x + 3/4) :
    ¬∃ x : ℝ, f x = 0 := by
  intro h
  rcases h with ⟨x, hx⟩
  have h_eq : x^6 - x^5 + x^4 - x^3 + x^2 - x + 3/4 = 0 := by
    rw [hf] at hx
    simpa using hx
  nlinarith [sq_nonneg (x^3 - x^2 / 2), sq_nonneg (x^2 - x / 2 - 1 / 2), sq_nonneg (x - 1 / 2), sq_nonneg (x^3 - x / 2 - 1 / 2), sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x^3 - 1), sq_nonneg (x - 1/2), sq_nonneg (x^2 - x + 1/2)]