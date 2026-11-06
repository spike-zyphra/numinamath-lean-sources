import Mathlib

/-What is the length of the segment of the number line whose endpoints satisfy $|x-\sqrt[5]{16}|=3$?-/
theorem algebra_14602 (x y : ℝ) (hx : |x - 16 ^ ((1 : ℝ) / 5)| = 3) (hy : |y - 16 ^ ((1 : ℝ) / 5)| = 3) (hxy : x > y):
    x - y = 6 := by
  rw [abs_eq] at hx hy
  rcases hx with (r₁ | r₂)
  . rcases hy with (r₃ | r₄)
    . -- x = 16 ^ ((1 : ℝ) / 5) + 3, y = 16 ^ ((1 : ℝ) / 5) + 3
      -- it is impossible, because x > y
      absurd hxy
      rw [r₁.symm] at r₃
      linarith
    . -- x = 16 ^ ((1 : ℝ) / 5) + 3, y = 16 ^ ((1 : ℝ) / 5) - 3
      rw [r₁.symm] at r₄
      linarith
  . rcases hy with (r₃ | r₄)
    . -- x = 16 ^ ((1 : ℝ) / 5) - 3, y = 16 ^ ((1 : ℝ) / 5) + 3
      -- it means x < y, which is impossible
      absurd hxy
      rw [r₃.symm] at r₂
      linarith
    . -- x = 16 ^ ((1 : ℝ) / 5) - 3, y = 16 ^ ((1 : ℝ) / 5) - 3
      -- x = y, which is impossible
      absurd hxy
      rw [r₂.symm] at r₄
      linarith
  repeat positivity
