import Mathlib
open Real

/- The lengths of two line segments are a units and b units respectively. Then the
correct relation between them is:
(A) (a+b)/2 > √ab (B) (a+b)/2 < √ab (C) (a+b)/2 = √ab
(D) (a+b)/2 ≤ √ab (E) (a+b)/2 ≥ √ab -/
theorem inequalities_95081 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
(a + b) / 2 ≥ sqrt (a * b) := by
  -- preparing some inequalities
  have hab:0≤ a*b:= le_of_lt $ mul_pos ha hb
  apply le_of_pow_le_pow_left₀ (by norm_num:2≠0)
  -- proving 0 ≤ (a + b) / 2
  · rw [← mul_le_mul_right ((by norm_num):(0:ℝ)<2)];simp
    rw[(by simp:(0:ℝ)=0+0)]
    exact add_le_add (le_of_lt ha) (le_of_lt hb)
  -- rearranging the terms
  rw [sq_sqrt hab,div_pow]
  norm_num
  rw [← mul_le_mul_right ((by norm_num):(0:ℝ)<4)];simp
  rw [add_pow_two]
  rw [← mul_le_mul_right ((by norm_num):(0:ℝ)<4)];simp
  rw [← sub_le_sub_iff_right (a*b*4)]
  have h1:a ^ 2 + 2 * a * b + b ^ 2 - a * b * 4= (a - b) ^ 2 := by ring
  rw [h1];simp
  exact sq_nonneg (a-b)