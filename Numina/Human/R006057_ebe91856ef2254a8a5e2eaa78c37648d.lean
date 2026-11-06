import Mathlib

open Real
set_option linter.unusedVariables false
/- Question: Two ants, one starting at (−1,1), the other at (1,1), walk to the right along the parabola y=x^2 such that their midpoint moves along the line y=1 with constant speed 1. When the left ant first hits the line y=1/2, its speed is 3√3-3. -/
theorem algebra_611319 (f : ℝ → ℝ) (x1 y1 x2 y2 v1 v2 w1 w2: ℝ) (hf : f = fun x => x ^ 2) (h1 : y1 = f x1) (h2 : y2 = f x2) (h_loc_y : (y1 + y2) / 2 = 1) (h_vel_x : (v1 + v2) / 2 = 1) (h_vel_y : (w1 + w2) / 2 = 0) (hs1 : w1 / v1 = deriv f x1) (hs2 : w2 / v2 = deriv f x2) (h : y1 = 1 / 2 ∧ x1 > -1 ∧ x1 < 0 ∧ x2 > 1) (v1_non_zero : v1 ≠ 0) (v2_non_zero : v2 ≠ 0) (w1_non_zero : w1 ≠ 0) (w2_non_zero : w2 ≠ 0): √(v1 ^ 2 + w1 ^ 2) = 3 * (sqrt 3) - 3 := by
  have aux1 : y1 = x1 ^ 2 := by rw [h1, hf]
  have aux2 : y2 = x2 ^ 2 := by rw [h2, hf]
  -- First show that the left ant is at (-√2/2,1/2)
  have left_ant_loc : x1 = - sqrt (1 / 2) ∧ y1 = 1 / 2 := by
    constructor
    have tmp1 :  x1 ^ 2 = 1 / 2 := by
      linarith
    have tmp2 : abs x1 = sqrt (1 / 2) := by
      rw [← tmp1]
      rw [sqrt_sq_eq_abs]
    have tmp3 : x1 = sqrt (1 / 2) ∨ x1 = - sqrt (1 / 2) := by
      rw [abs_eq] at tmp2
      exact tmp2
      norm_num
    rcases tmp3 with (hpos | hneg)
    · rw [hpos] at h
      have : sqrt (1 / 2) > 0 := sqrt_pos.2 (by norm_num)
      linarith
    · exact hneg
    linarith
  -- Then show that the right ant is at (√6/2,3/2)
  have right_ant_loc : x2 = sqrt (3 / 2) ∧ y2 = 3 / 2 := by
    have tmp1 : y1 + y2 = 2 := by
      linarith
    have tmp2 : y2 = 3 / 2 := by
      linarith
    constructor
    have tmp3 :  x2 ^ 2 = 3 / 2 := by
      linarith
    have tmp4 : abs x2 = sqrt (3 / 2) := by
      rw [← tmp3]
      rw [sqrt_sq_eq_abs]
    have tmp5 : x2 = sqrt (3 / 2) ∨ x2 = - sqrt (3 / 2) := by
      rw [abs_eq] at tmp4
      exact tmp4
      exact sqrt_nonneg (3 / 2)
    rcases tmp5 with (hpos | hneg)
    · exact hpos
    · rw [hneg] at h
      have : sqrt (3 / 2) > 0 := sqrt_pos.2 (by norm_num)
      linarith
    exact tmp2
  -- Calculate the derivative
  have aux3 : deriv f = fun x => 2 * x := by
    rw [hf]
    funext x
    simp [deriv_pow]
  -- Eliminate w1 and w2
  have aux4 : w1 / v1 = -2 * sqrt (1 / 2) := by
    rw [hs1, aux3]
    linarith
  have aux5 : w2 / v2 = 2 * sqrt (3 / 2) := by
    rw [hs2, aux3]
    linarith
  have aux6 : w1 = -2 * sqrt (1 / 2) * v1 := by
    rw [← aux4]
    rw [div_mul, div_self]
    linarith
    exact v1_non_zero
  have aux7 : w2 = 2 * sqrt (3 / 2) * v2 := by
    rw [← aux5]
    rw [div_mul, div_self]
    linarith
    exact v2_non_zero
  -- Solve v1 and v2
  have aux8 : v1 + v2 = 2 := by
    linarith
  have aux9 : 2 * sqrt (1 / 2) * v1 - 2 * sqrt (3 / 2) * v2 = 0 := by
    linarith
  have aux10 : 2 * sqrt (3 / 2) * v1 + 2 * sqrt (3 / 2) * v2 = 2 * sqrt (3 / 2) * 2 := by
    rw [← mul_add]
    simp
    exact aux8
  have aux11 : 2 * sqrt (1 / 2) * v1 + 2 * sqrt (3 / 2) * v1 = 2 * sqrt (3 / 2) * 2 := by
    rw [← aux10]
    rw [add_comm]
    simp
    have aux12 : 2 * (√2)⁻¹ * v1 = 2 * sqrt (1 / 2) * v1 := by
      simp
    have aux13 : 2 * (√3 / √2) * v2 = 2 * sqrt (3 / 2) * v2 := by
      simp
    rw [aux12, aux13]
    linarith
  have aux14 : v1 + √3 * v1 = √3 * 2 := by
    field_simp at aux11
    rw [mul_comm] at aux11
    rw [← mul_assoc] at aux11
    simp at aux11
    rw [mul_assoc] at aux11
    rw [mul_assoc] at aux11
    rw [← mul_add] at aux11
    simp at aux11
    exact aux11
  have aux15 : v1 = √3 * 2 / (1 + √3) := by
    nth_rw 1 [← one_mul v1] at aux14
    rw [← right_distrib] at aux14
    field_simp
    linarith
  have aux16 : √6 = √2 * √3 := by
    rw [← sqrt_mul]
    norm_num
    linarith
  have v1_eq : v1 = 3 - √3 := by
    rw [aux15]
    field_simp
    ring_nf
    simp
  have w1_eq : w1 = √6 - 3 * √2 := by
    rw [aux6]
    field_simp
    rw [v1_eq]
    ring_nf
    rw [aux16]
    nth_rw 2 [mul_comm]
    rw [← mul_assoc]
    simp
    linarith
  -- Plug v1 and w1 into the equation
  rw [v1_eq, w1_eq]
  have aux17 : (3 - √3) ^ 2 + (√6 - 3 * √2) ^ 2 = (3 * √3 - 3) ^ 2 := by
    rw [aux16]
    ring_nf
    field_simp
    ring
  rw [aux17]
  rw [sqrt_sq]
  norm_num
