import Mathlib

/- 26th Swedish 1986 Problem 1 Show that x 6 - x 5 + x 4 - x 3 + x 2 - x + 3/4 has no real zeros. -/
theorem algebra_151566 (f : ℝ → ℝ) (hf : f = fun x => x^6 - x^5 + x^4 - x^3 + x^2 - x + 3/4) :
    ¬∃ x : ℝ, f x = 0 := by
    intro h
    rcases h with ⟨x, hx⟩
    -- complete the square
    have : f x ≥ 3 / 8 := by calc
      3/8 ≤ x^2 * (x * (x - 1/2))^2 + (3/4) * (x * (x - 2/3))^2 + (2/3) * (x - 3/4)^2 + 3/8 := by
        have sq₁ : (x - 3/4)^2 ≥ 0 := sq_nonneg _
        have sq₂ : (x * (x - 2/3))^2 ≥ 0 := sq_nonneg _
        have sq₃ : x^2 * (x * (x - 1/2))^2 ≥ 0 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
        linarith
      _ = x^6 - x^5 + x^4 - x^3 + x^2 - x + 3/4 := by ring
      _ = f x := by rw [hf]
    linarith