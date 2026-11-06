import Mathlib

open Real

theorem inequalities_214710 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    2 * sqrt 2 ≤ sqrt (a + b) * (1 / sqrt a + 1 / sqrt b) := by
  have h1 : 0 < sqrt a := by positivity
  have h2 : 0 < sqrt b := by positivity
  have h3 : sqrt a * sqrt b > 0 := by positivity
  have h4 : sqrt (a + b) > 0 := by positivity

  have h5 : sqrt (a + b) * (1 / sqrt a + 1 / sqrt b) = (sqrt (a + b) * (sqrt a + sqrt b)) / (sqrt a * sqrt b) := by
    field_simp [h1, h2]
    <;> ring_nf <;> field_simp [h1, h2]
    <;> ring_nf

  have h6 : (sqrt (a + b) * (1 / sqrt a + 1 / sqrt b)) ^ 2 ≥ 8 := by
    rw [h5]
    have h7 : (sqrt (a + b) * (sqrt a + sqrt b)) ^ 2 = (a + b) * (sqrt a + sqrt b) ^ 2 := by
      calc
        (sqrt (a + b) * (sqrt a + sqrt b)) ^ 2
          = (sqrt (a + b)) ^ 2 * (sqrt a + sqrt b) ^ 2 := by ring_nf
        _ = (a + b) * (sqrt a + sqrt b) ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
    have h8 : (sqrt a * sqrt b) ^ 2 = a * b := by
      calc
        (sqrt a * sqrt b) ^ 2 = (sqrt a) ^ 2 * (sqrt b) ^ 2 := by ring_nf
        _ = a * b := by
          rw [Real.sq_sqrt (by linarith), Real.sq_sqrt (by linarith)]
    have h9 : (sqrt (a + b) * (sqrt a + sqrt b) / (sqrt a * sqrt b)) ^ 2 = (sqrt (a + b) * (sqrt a + sqrt b)) ^ 2 / ((sqrt a * sqrt b) ^ 2) := by
      field_simp [h1, h2, h3]
      <;> ring_nf <;> field_simp [h1, h2, h3]

    rw [h9, h7, h8]

    have h10 : (sqrt a + sqrt b) ^ 2 = a + b + 2 * (sqrt (a * b)) := by
      have h11 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
      have h12 : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
      have h13 : sqrt (a * b) = sqrt a * sqrt b := by
        rw [Real.sqrt_mul (by linarith)]
      nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a * sqrt b), Real.sqrt_nonneg (a * b)]

    rw [h10]
    have h11 : (a + b) * (a + b + 2 * sqrt (a * b)) ≥ 8 * (a * b) := by
      nlinarith [sq_nonneg (sqrt (a * b) - (a + b) / 2), sq_nonneg (sqrt a - sqrt b), Real.sqrt_nonneg (a * b), Real.mul_self_sqrt (by positivity : 0 ≤ (a * b : ℝ)), sq_nonneg (a - b)]

    have h14 : (a + b) * (a + b + 2 * sqrt (a * b)) / (a * b) ≥ 8 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith

    linarith

  have h7 : (sqrt (a + b) * (1 / sqrt a + 1 / sqrt b)) ^ 2 ≥ (2 * sqrt 2) ^ 2 := by
    linarith [h6, sq_nonneg (2 * sqrt 2), sq_nonneg (sqrt (a + b) * (1 / sqrt a + 1 / sqrt b)), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)]

  have h8 : sqrt (a + b) * (1 / sqrt a + 1 / sqrt b) ≥ 0 := by positivity
  have h9 : 2 * sqrt 2 ≥ 0 := by positivity

  nlinarith [Real.sqrt_nonneg 2, sq_nonneg (sqrt (a + b) * (1 / sqrt a + 1 / sqrt b) - 2 * sqrt 2), sq_nonneg (sqrt (a + b) * (1 / sqrt a + 1 / sqrt b) + 2 * sqrt 2)]