import Mathlib

open Real

theorem algebra_603892 (x : ℝ) (hx : 0 < x ∧ x < 1) :
    ((sqrt (1 + x)) / (sqrt (1 + x) - sqrt (1 - x)) + (1 - x) / (sqrt (1 - x ^ 2) + x - 1)) *
    (sqrt ((1 / x ^ 2) - 1) - 1 / x) = -1 := by
  have hx1 : 0 < x := hx.1
  have hx2 : x < 1 := hx.2
  have h1 : 0 < 1 + x := by linarith
  have h2 : 0 < 1 - x := by linarith
  have h3 : 0 < 1 - x ^ 2 := by nlinarith
  have h4 : sqrt (1 + x) > 0 := by positivity
  have h5 : sqrt (1 - x) > 0 := by positivity
  have h6 : sqrt (1 - x ^ 2) > 0 := by positivity
  have h7 : sqrt (1 + x) - sqrt (1 - x) ≠ 0 := by 
    have h8 : sqrt (1 + x) > sqrt (1 - x) := by
      apply Real.sqrt_lt_sqrt
      all_goals linarith
    have h9 : sqrt (1 + x) - sqrt (1 - x) > 0 := by linarith
    linarith
  have h8 : sqrt (1 - x^2) + x - 1 ≠ 0 := by
    by_contra h
    have h9 : sqrt (1 - x^2) = 1 - x := by linarith
    have h10 : (sqrt (1 - x^2)) ^ 2 = (1 - x) ^ 2 := by rw [h9]
    rw [Real.sq_sqrt (by nlinarith)] at h10
    have h11 : 1 - x^2 = (1 - x) ^ 2 := by nlinarith
    ring_nf at h11
    have h12 : 2 * x * (x - 1) = 0 := by nlinarith
    cases' (mul_eq_zero.mp h12) with h13 h14
    ·
      have h15 : x = 0 := by nlinarith
      linarith
    ·
      have h16 : x = 1 := by linarith
      linarith
  have part1 : (sqrt (1 + x)) / (sqrt (1 + x) - sqrt (1 - x)) + (1 - x) / (sqrt (1 - x ^ 2) + x - 1) = (1 + sqrt (1 - x^2)) / x := by
    have eq1 : (sqrt (1 + x)) / (sqrt (1 + x) - sqrt (1 - x)) = (1 + x + sqrt (1 - x^2)) / (2 * x) := by
      have h9 : sqrt (1 - x^2) = sqrt ((1 + x) * (1 - x)) := by
        rw [show (1 - x^2) = (1 + x) * (1 - x) by ring_nf]
      have h10 : sqrt ((1 + x) * (1 - x)) = sqrt (1 + x) * sqrt (1 - x) := by
        rw [Real.sqrt_mul]
        all_goals nlinarith
      rw [h10] at h9
      have h11 : sqrt (1 + x) - sqrt (1 - x) ≠ 0 := h7
      field_simp [h11]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 + x by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x by nlinarith), Real.sqrt_pos.mpr (show (0 : ℝ) < 1 + x by nlinarith), Real.sqrt_pos.mpr (show (0 : ℝ) < 1 - x by nlinarith), Real.sqrt_nonneg (1 + x), Real.sqrt_nonneg (1 - x), h9]
    have eq2 : (1 - x) / (sqrt (1 - x^2) + x - 1) = (sqrt (1 - x^2) + (1 - x)) / (2 * x) := by
      have h14 : sqrt (1 - x^2) + x - 1 ≠ 0 := h8
      field_simp [h14]
      have h9 : sqrt (1 - x^2) = sqrt ((1 + x) * (1 - x)) := by
        rw [show (1 - x^2) = (1 + x) * (1 - x) by ring_nf]
      have h10 : sqrt ((1 + x) * (1 - x)) = sqrt (1 + x) * sqrt (1 - x) := by
        rw [Real.sqrt_mul]
        all_goals nlinarith
      rw [h10] at h9
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith), Real.sqrt_pos.mpr (show (0 : ℝ) < 1 - x^2 by nlinarith), Real.sqrt_nonneg (1 - x^2), h9]
    rw [eq1, eq2]
    field_simp [show x ≠ 0 by nlinarith]
    <;> ring_nf <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1 - x^2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith)]
  have part2 : sqrt ((1 / x^2) - 1) - 1 / x = (sqrt (1 - x^2) - 1) / x := by
    have h11 : sqrt ((1 / x^2) - 1) = sqrt (1 - x^2) / x := by
      have h13 : (1 / x^2) - 1 = (1 - x^2) / x^2 := by
        field_simp [show x ≠ 0 by nlinarith]
        <;> nlinarith
      rw [h13]
      have h14 : sqrt ((1 - x^2) / x^2) = sqrt (1 - x^2) / sqrt (x^2) := by
        field_simp [Real.sqrt_div]
      rw [h14]
      have h15 : sqrt (x^2) = x := by
        rw [Real.sqrt_sq (show 0 ≤ x by linarith)]
      rw [h15]
    rw [h11]
    <;> field_simp [show x ≠ 0 by nlinarith]
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 1 - x^2 by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith)]
  rw [part1, part2]
  field_simp [show x ≠ 0 by nlinarith, Real.sqrt_pos.mpr h3, show 0 < (1 - x^2 : ℝ) by nlinarith]
  <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 1 - x^2 by nlinarith), Real.sqrt_pos.mpr h3]