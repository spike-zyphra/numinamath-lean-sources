import Mathlib
theorem algebra_611170 : IsGreatest {a : ℝ | ∃ x y z : ℝ, 2 * x ^ 2 + y ^ 2 + z ^ 2 = 2 * x - 4 * y + 2 * x * z - 5 ∧ a = x - y + z} 4:= by
  constructor
  · -- Show 4 is in the set
    use 1, -2, 1
    constructor 
    · -- Show 2*1^2 + (-2)^2 + 1^2 = 2*1 - 4*(-2) + 2*1*1 - 5
      norm_num
    · -- Show 4 = 1 - (-2) + 1
      norm_num 
  · -- Show there is no greater element in the set
    intro a h
    rcases h with ⟨x, y, z, h3, h4⟩
    have h5 : (z - x) ^ 2 + (x - 1) ^ 2 + (y + 2) ^ 2 = 0 := by 
      nlinarith
    have hx1 : z - x = 0 := by
      nlinarith [sq_nonneg (z - x), sq_nonneg (x - 1), sq_nonneg (y + 2)]
    have hx2 : x - 1 = 0 := by 
      nlinarith [sq_nonneg (z - x), sq_nonneg (x - 1), sq_nonneg (y + 2)]
    have hx3 : y + 2 = 0 := by 
      nlinarith [sq_nonneg (z - x), sq_nonneg (x - 1), sq_nonneg (y + 2)]
    have hx4 : x = 1 := by linarith 
    have hz1 : z = 1 := by 
      linarith [show x = 1 by linarith, hx1]
    have hy1 : y = -2 := by linarith 
    have ha : a = 4 := by
      rw [show x = 1 by linarith, show y = -2 by linarith, show z = 1 by linarith] at h4 
      linarith 
    linarith [ha]