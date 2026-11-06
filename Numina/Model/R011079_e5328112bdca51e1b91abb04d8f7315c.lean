import Mathlib

theorem algebra_10614 (f : ℝ → ℝ → ℝ)
    (h₀ : ∀ x y, f x y = x ^ 2 + 2 * y ^ 2 + 6 * x - 4 * y + 22) :
    IsLeast {z | ∃ x y, z = f x y} 11 := by 
  constructor
  · -- Show 11 is in the image.
    use -3, 1
    norm_num [h₀]
  · -- Show there is no smaller value.
    intro z h
    rcases h with ⟨x, y, hz⟩
    have h1 : f x y = x ^ 2 + 2 * y ^ 2 + 6 * x - 4 * y + 22 := h₀ x y
    rw [h1] at hz 
    nlinarith [sq_nonneg (x + 3), sq_nonneg (y - 1)]