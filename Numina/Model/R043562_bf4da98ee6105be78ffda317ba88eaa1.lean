import Mathlib

open Real

theorem algebra_11185
    {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a^2 + b^2 = 8 * a * b) :
    |((a + b) / (a - b))| = √ 15 / 3 := by
  have h1 : a - b ≠ 0 := by
    by_contra h2
    have h4 : a = b := by linarith
    have h5 : a^2 + b^2 = 8 * a * b := by linarith [h]
    rw [show b = a by linarith [h4]] at h5
    have h6 : 2 * a^2 = 8 * a^2 := by nlinarith
    have h7 : 6 * a^2 = 0 := by
      nlinarith
    have h8 : a^2 = 0 := by
      nlinarith
    have h9 : a = 0 := by
      nlinarith
    contradiction
  have h2 : |((a + b) / (a - b))| = Real.sqrt ((a + b) ^ 2 / (a - b) ^ 2) := by
    have h3 : |((a + b) / (a - b))| = Real.sqrt (((a + b) / (a - b)) ^ 2) := by
      rw [Real.sqrt_sq_eq_abs]
    have h4 : ((a + b) / (a - b)) ^ 2 = (a + b) ^ 2 / (a - b) ^ 2 := by
      field_simp [show a - b ≠ 0 by assumption]
    rw [h4] at h3
    exact h3
  have eq2 : (a + b) ^ 2 / (a - b) ^ 2 = 5 / 3 := by
    have eq3 : (a + b) ^ 2 = 10 * (a * b) := by
      nlinarith [h, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
    have eq4 : (a - b) ^ 2 = 6 * (a * b) := by
      nlinarith [h, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb]
    have eq5 : (a + b) ^ 2 / (a - b) ^ 2 = 10 * (a * b) / (6 * (a * b)) := by 
      rw [eq3, eq4]
    rw [eq5]
    have h10 : a * b ≠ 0 := by
      apply mul_ne_zero 
      exact ha 
      exact hb
    have eq6 : 10 * (a * b) / (6 * (a * b)) = 5 / 3 := by
      have h11 : a * b ≠ 0 := h10 
      have h12 : 6 * (a * b) ≠ 0 := by 
        intro h 
        apply h11 
        linarith 
      field_simp [h11]
      <;> ring_nf
    exact eq6
  rw [h2, eq2]
  have h3 : Real.sqrt (5 / 3) = Real.sqrt 15 / 3 := by
    have h4 : Real.sqrt (5 / 3) ^ 2 = 5 / 3 := by
      rw [Real.sq_sqrt]
      all_goals norm_num
    have h5 : (Real.sqrt 15 / 3) ^ 2 = 5 / 3 := by
      calc
        (Real.sqrt 15 / 3) ^ 2 = (Real.sqrt 15) ^ 2 / 9 := by ring_nf
        _ = 15 / 9 := by 
          rw [Real.sq_sqrt]
          all_goals norm_num 
        _ = 5 / 3 := by norm_num
    have h7 : Real.sqrt (5 / 3) ≥ 0 := Real.sqrt_nonneg (5 / 3)
    have h8 : Real.sqrt 15 / 3 ≥ 0 := by
      positivity 
    have h9 : Real.sqrt (5 / 3) = Real.sqrt 15 / 3 := by 
      nlinarith [h4, h5, Real.sqrt_nonneg (5 / 3), Real.sqrt_nonneg 15]
    exact h9
  rw [h3]