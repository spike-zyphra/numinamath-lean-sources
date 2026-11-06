import Mathlib

theorem algebra_159914 (x : ℝ) (hx : x ≠ 0) :
    (x^2 + 4) / (x * Real.sqrt (4 + ((x^2 - 4) / (2 * x))^2)) =
    if x < 0 then -2 else 2 := by
  have h1 : 4 + ((x^2 - 4) / (2 * x))^2 = ((x^2 + 4) ^ 2) / (4 * x^2) := by
    field_simp
    ring
  have h2 : Real.sqrt (4 + ((x ^ 2 - 4) / (2 * x)) ^ 2) = (x ^ 2 + 4) / (2 * |x|) := by
    rw [h1]
    have h3 : Real.sqrt (((x ^ 2 + 4) ^ 2) / (4 * x^2)) = Real.sqrt ((x^2 + 4) ^ 2) / Real.sqrt (4 * x^2) := by
      field_simp [Real.sqrt_div]
    rw [h3]
    have h4 : Real.sqrt ((x^2 + 4) ^ 2) = x^2 + 4 := by
      rw [Real.sqrt_sq (by positivity)]
    have h5 : Real.sqrt (4 * x^2) = 2 * |x| := by
      calc
        Real.sqrt (4 * x^2) = Real.sqrt (4 * (x^2)) := by ring_nf
        _ = Real.sqrt (4) * Real.sqrt (x^2) := by rw [Real.sqrt_mul (by norm_num)]
        _ = (2 : ℝ) * |x| := by 
          have h6 : Real.sqrt (4 : ℝ) = (2 : ℝ) := by 
            rw [Real.sqrt_eq_cases]
            all_goals norm_num
          have h7 : Real.sqrt (x^2) = |x| := by 
            rw [Real.sqrt_sq_eq_abs]
          rw [h6, h7]
    rw [h4, h5]
    <;> ring_nf 
  rw [h2]
  by_cases h3 : x < 0 
  · -- Assume x < 0
    have h4 : |x| = -x := abs_of_neg h3
    rw [h4]
    have eq1 : (x^2 + 4) / (x * ((x ^ 2 + 4) / (2 * -x))) = -2 := by
      have hx5 : x < 0 := h3
      have hx6 : x ≠ 0 := hx
      have hx7 : x ^ 2 + 4 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hx6, show (-x : ℝ) ≠ 0 by nlinarith]
      <;> ring_nf 
    rw [eq1]
    simp [h3]
  · -- Assume x ≥ 0
    have h4 : x ≥ 0 := by linarith
    have h5 : |x| = x := abs_of_nonneg h4
    rw [h5]
    have h9 : x > 0 := by 
      by_contra h9
      push_neg at h9
      have : x = 0 := by linarith
      contradiction
    have eq1 : (x^2 + 4) / (x * ((x ^ 2 + 4) / (2 * x))) = 2 := by
      have hx5 : x ≠ 0 := hx
      have hx6 : x ^ 2 + 4 ≠ 0 := by
        nlinarith [sq_nonneg x]
      field_simp [hx5, show (x : ℝ) ≠ 0 by exact hx]
      <;> ring_nf
    rw [eq1]
    simp [h3]