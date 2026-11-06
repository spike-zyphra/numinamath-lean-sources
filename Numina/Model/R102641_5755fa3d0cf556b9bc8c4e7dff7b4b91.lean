import Mathlib

theorem algebra_106181 (f : ℝ → ℝ) (hf : f = fun x => x^4 - 5 * x^3 + 3 * x^2 - 7 * x + 1) :
    ¬∃ x, x < 0 ∧ f x = 0 := by 
  rintro ⟨x, ⟨hx1, hx2⟩⟩
  rw [hf] at hx2
  simp at hx2
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x + 1), sq_nonneg (x ^ 2 - x), sq_nonneg (x ^ 2 + 1), sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 2)]