import Mathlib

theorem algebra_321720 (f : ℝ → ℝ) (hf : f = fun x => 2 * x ^ 2 - x - 3) :
    IsLeast {y | ∃ x, y = f x} (-3 - 1 / 8) := by
  constructor
  · -- First, we prove that -3 - 1/8 is in the image of f
    use 1 / 4
    rw [hf]
    norm_num
  · -- Now, we show that -3 - 1/8 is the smallest value in the image
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hf] at hx
    simp at hx
    have h : 2 * (x - 1 / 4) ^ 2 ≥ 0 := by
      apply mul_nonneg
      norm_num
      apply pow_two_nonneg
    linarith [sq_nonneg (x - 1 / 4)]