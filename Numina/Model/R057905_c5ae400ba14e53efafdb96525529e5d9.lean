import Mathlib

theorem inequalities_224371 (x y z : ℝ) (h₀ : x + y + z = 0) (h₁ : abs x + abs y + abs z ≤ 1) :
    x + y / 3 + z / 5 ≤ 2 / 5 := by
  by_cases hx : x ≥ 0
  · -- if $x \geq 0$.
    by_cases hy : y ≥ 0
    · -- if $x \geq 0, y \geq 0$.
      by_cases hz : z ≥ 0
      · -- all numbers are non-negative. so all must be zero.
        have h2 : x = 0 := by linarith [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg hz]
        have h3 : y = 0 := by linarith [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg hz]
        have h4 : z = 0 := by linarith [abs_of_nonneg hx, abs_of_nonneg hy, abs_of_nonneg hz]
        rw [h2, h3, h4]
        norm_num
      · -- if $x \geq 0, y \geq 0, z < 0$.
        have hz' : z < 0 := by linarith
        have h2 : abs x = x := abs_of_nonneg hx
        have h3 : abs y = y := abs_of_nonneg hy
        have h4 : abs z = -z := abs_of_neg hz'
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y), sq_nonneg (x + y - 1 / 2)]
    · -- if $x \geq 0. y < 0$.
      by_cases hz : z ≥ 0
      · -- if $x \geq 0, y < 0, z \geq 0$.
        have hy' : y < 0 := by linarith
        have h2 : abs x = x := abs_of_nonneg hx
        have h3 : abs y = -y := abs_of_neg hy'
        have h4 : abs z = z := abs_of_nonneg hz
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x), sq_nonneg (y + 1 / 2), sq_nonneg (z)]
      · -- if $x \geq 0, y < 0, z < 0$.
        have hy' : y < 0 := by linarith
        have hz' : z < 0 := by linarith
        have h2 : abs x = x := abs_of_nonneg hx
        have h3 : abs y = -y := abs_of_neg hy'
        have h4 : abs z = -z := abs_of_neg hz'
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z + 1 / 2)]
  · -- if $x < 0$.
    by_cases hy : y ≥ 0
    · -- if $x < 0, y \geq 0$.
      by_cases hz : z ≥ 0
      · -- if $x < 0, y \geq 0, z \geq 0$.
        have hx' : x < 0 := by linarith
        have h2 : abs x = -x := abs_of_neg hx'
        have h3 : abs y = y := abs_of_nonneg hy
        have h4 : abs z = z := abs_of_nonneg hz
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y - 1), sq_nonneg (z)]
      · -- if $x < 0, y \geq 0, z < 0$.
        have hz' : z < 0 := by linarith
        have h2 : abs x = -x := abs_of_neg (show x < 0 by linarith)
        have h3 : abs y = y := abs_of_nonneg hy
        have h4 : abs z = -z := abs_of_neg hz'
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y), sq_nonneg (z + 1 / 2)]
    · -- if $x < 0, y < 0$.
      by_cases hz : z ≥ 0
      · -- if $x < 0, y < 0, z \geq 0$.
        have hy' : y < 0 := by linarith
        have h2 : abs x = -x := abs_of_neg (show x < 0 by linarith)
        have h3 : abs y = -y := abs_of_neg hy'
        have h4 : abs z = z := abs_of_nonneg hz
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x + 1 / 2), sq_nonneg (y + 1 / 2), sq_nonneg (z)]
      · -- if $x < 0, y < 0, z < 0$.
        have hy' : y < 0 := by linarith
        have hz' : z < 0 := by linarith
        have h2 : abs x = -x := abs_of_neg (show x < 0 by linarith)
        have h3 : abs y = -y := abs_of_neg hy'
        have h4 : abs z = -z := abs_of_neg hz'
        rw [h2, h3, h4] at h₁
        nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z)]