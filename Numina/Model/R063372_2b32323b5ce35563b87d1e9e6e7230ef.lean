import Mathlib

open Real

theorem inequalities_315082 (a b : ℝ) (ha : 0 < a) (hb : a < b ∧ b < 1) :
    2 * sqrt 2 ≤ sqrt (a^2 + b^2) + sqrt (a^2 + (1 - b)^2) +
    sqrt ((1 - a)^2 + b^2) + sqrt ((1 - a)^2 + (1 - b)^2) := by
  have h1 : 0 < b := by linarith
  have h2 : b < 1 := hb.right
  have h3 : 0 < 1 - b := by linarith
  have h4 : 0 < 1 - a := by linarith
  have h5 : sqrt (a^2 + b^2) ≥ (a + b) / Real.sqrt 2 := by
    have h6 : (a + b) ^ 2 ≤ 2 * (a^2 + b^2) := by
      nlinarith [sq_nonneg (a - b)]
    have h7 : (a + b) / Real.sqrt 2 ≤ Real.sqrt (a^2 + b^2) := by
      have h8 : ((a + b) / Real.sqrt 2) ^ 2 ≤ a^2 + b^2 := by
        calc
          ((a + b) / Real.sqrt 2) ^ 2 = (a + b) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) := by ring_nf
          _ = (a + b) ^ 2 / (2 : ℝ) := by rw [Real.mul_self_sqrt]; linarith
          _ ≤ a^2 + b^2 := by nlinarith [h6]
      have h9 : (a + b) / Real.sqrt 2 ≤ Real.sqrt (a^2 + b^2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    linarith
  have h5' : sqrt (a^2 + (1 - b)^2) ≥ (a + (1 - b)) / Real.sqrt 2 := by
    have h6' : (a + (1 - b)) ^ 2 ≤ 2 * (a^2 + (1 - b)^2) := by
      nlinarith [sq_nonneg (a - (1 - b))]
    have h7' : (a + (1 - b)) / Real.sqrt 2 ≤ Real.sqrt (a^2 + (1 - b)^2) := by
      have h8' : ((a + (1 - b)) / Real.sqrt 2) ^ 2 ≤ a^2 + (1 - b)^2 := by
        calc
          ((a + (1 - b)) / Real.sqrt 2) ^ 2 = (a + (1 - b)) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) := by ring_nf
          _ = (a + (1 - b)) ^ 2 / (2 : ℝ) := by rw [Real.mul_self_sqrt]; linarith
          _ ≤ a^2 + (1 - b)^2 := by nlinarith [h6']
      have h9' : (a + (1 - b)) / Real.sqrt 2 ≤ Real.sqrt (a^2 + (1 - b)^2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    linarith
  have h5'' : sqrt ((1 - a)^2 + b^2) ≥ ((1 - a) + b) / Real.sqrt 2 := by
    have h6'' : ((1 - a) + b) ^ 2 ≤ 2 * ((1 - a)^2 + b^2) := by
      nlinarith [sq_nonneg ((1 - a) - b)]
    have h7'' : ((1 - a) + b) / Real.sqrt 2 ≤ Real.sqrt ((1 - a)^2 + b^2) := by
      have h8'' : (((1 - a) + b) / Real.sqrt 2) ^ 2 ≤ (1 - a)^2 + b^2 := by
        calc
          (((1 - a) + b) / Real.sqrt 2) ^ 2 = ((1 - a) + b) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) := by  ring_nf
          _ = ((1 - a) + b) ^ 2 / (2 : ℝ) := by rw [Real.mul_self_sqrt]; linarith
          _ ≤ (1 - a)^2 + b^2 := by nlinarith [h6'']
      have h9'' : ((1 - a) + b) / Real.sqrt 2 ≤ Real.sqrt ((1 - a)^2 + b^2) := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    linarith
  have h5''' : sqrt ((1 - a)^2 + (1 - b)^2) ≥ ((1 - a) + (1 - b)) / Real.sqrt 2 := by
    have h6''' : ((1 - a) + (1 - b)) ^ 2 ≤ 2 * ((1 - a)^2 + (1 - b)^2) := by
      nlinarith [sq_nonneg ((1 - a) - (1 - b))]
    have h7''' : ((1 - a) + (1 - b)) / Real.sqrt 2 ≤ Real.sqrt ((1 - a)^2 + (1 - b)^2) := by
      have h8''' : (((1 - a) + (1 - b)) / Real.sqrt 2) ^ 2 ≤ (1 - a)^2 + (1 - b)^2 := by
        calc
          (((1 - a) + (1 - b)) / Real.sqrt 2) ^ 2 = ((1 - a) + (1 - b)) ^ 2 / (Real.sqrt 2 * Real.sqrt 2) :=  by  ring_nf
          _ = ((1 - a) + (1 - b)) ^ 2 / (2 : ℝ) :=  by  rw [Real.mul_self_sqrt];  linarith
          _ ≤ (1 - a)^2 + (1 - b)^2 :=  by  nlinarith [h6''']
      have  h9''' : ((1 - a) + (1 - b)) / Real.sqrt 2 ≤ Real.sqrt ((1 - a)^2 + (1 - b)^2) :=  by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    linarith
  have sum_ineq : sqrt (a^2 + b^2) + sqrt (a^2 + (1 - b)^2) + sqrt ((1 - a)^2 + b^2) + sqrt ((1 - a)^2 + (1 - b)^2) ≥ (a + b) / Real.sqrt 2 + (a + (1 - b)) / Real.sqrt 2 + ((1 - a) + b) / Real.sqrt 2 + ((1 - a) + (1 - b)) / Real.sqrt 2 := by
    linarith [h5, h5', h5'', h5''']
  have eq1 : (a + b) / Real.sqrt 2 + (a + (1 - b)) / Real.sqrt 2 + ((1 - a) + b) / Real.sqrt 2 + ((1 - a) + (1 - b)) / Real.sqrt 2 = 2 * Real.sqrt 2 := by
    field_simp
    ring_nf
    <;> nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
  linarith [sum_ineq, eq1]