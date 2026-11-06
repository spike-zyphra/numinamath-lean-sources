import Mathlib

theorem algebra_149794 (f : ℝ → ℝ) (hf : f = fun x => x^4 - 12*x^3 + 63*x^2 - 102*x + 85) :
    ¬∃ x : ℝ, f x = 0 := by
  intro h
  rcases h with ⟨x, hx⟩
  have h_eq : f x = 0 := hx
  rw [hf] at h_eq
  simp at h_eq
  have h1 : x^4 - 12*x^3 + 63*x^2 - 102*x + 85 > 0 := by
    nlinarith [sq_nonneg (x^2 - 6*x), sq_nonneg (x - 1), sq_nonneg (x - 2), sq_nonneg (x - 3), sq_nonneg (x - 4), sq_nonneg (x - 5), sq_nonneg (x - 6), sq_nonneg (x + 1)]
  linarith