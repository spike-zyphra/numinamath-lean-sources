import Mathlib

/- What is the minimum value of $z$ if $z=x^2+2y^2+6x-4y+22?$ -/
theorem algebra_10614 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = x ^ 2 + 2 * y ^ 2 + 6 * x - 4 * y + 22) :
    IsLeast {z | ∃ x y, z = f x y} 11 := by
  refine' ⟨⟨-3, 1, by norm_num [h₀]⟩, fun z hz => _⟩
  rcases hz with ⟨x, y, rfl⟩
  simp_all only [h₀, exists_prop]
  linarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]