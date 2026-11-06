import Mathlib

open Real

theorem algebra_257088 {a b : ℝ} (ha : 0 < a) (hb : a < b)
    (x y : ℝ) (hx : x = sqrt (a + b) - sqrt b) (hy : y = sqrt b - sqrt (b - a)) :
    x < y := by 
  rw [hx, hy]
  have h1 : sqrt (a + b) + sqrt (b - a) < 2 * sqrt b := by
    have h2 : a + b > 0 := by linarith
    have h3 : b - a > 0 := by linarith
    have h4 : sqrt (a + b) > 0 := by apply sqrt_pos.mpr; linarith
    have h5 : sqrt (b - a) > 0 := by apply sqrt_pos.mpr; linarith
    have h6 : sqrt b > 0 := by apply sqrt_pos.mpr; linarith
    have h7 : sqrt (a + b) + sqrt (b - a) > 0 := by linarith
    have h8 : 2 * sqrt b > 0 := by linarith
    have h9 : (sqrt (a + b) + sqrt (b - a)) ^ 2 < (2 * sqrt b) ^ 2 := by
      have h10 : (sqrt (a + b) + sqrt (b - a)) ^ 2 = (sqrt (a + b)) ^ 2 + (sqrt (b - a)) ^ 2 + 2 * (sqrt (a + b) * sqrt (b - a)) := by ring
      have h11 : (sqrt b) ^ 2 = b := by apply sq_sqrt; linarith
      have h12 : (sqrt (a + b)) ^ 2 = a + b := by apply sq_sqrt; linarith
      have h13 : (sqrt (b - a)) ^ 2 = b - a := by apply sq_sqrt; linarith
      have h14 : sqrt (a + b) * sqrt (b - a) = sqrt ((a + b) * (b - a)) := by
        rw [← sqrt_mul (by linarith)]
        all_goals linarith
      have h15 : (sqrt (a + b) + sqrt (b - a)) ^ 2 = 2 * b + 2 * sqrt ((a + b) * (b - a)) := by
        rw [h10]
        have h16 : sqrt (a + b) * sqrt (b - a) = sqrt ((a + b) * (b - a)) := h14
        nlinarith [h12, h13, h16]
      have h16 : (2 * sqrt b) ^ 2 = 4 * b := by
        calc
          (2 * sqrt b) ^ 2 = 4 * (sqrt b) ^ 2 := by ring_nf
          _ = 4 * b := by rw [show (sqrt b) ^ 2 = b by apply sq_sqrt; linarith]
      rw [h15, h16]
      have h17 : sqrt ((a + b) * (b - a)) < b := by
        have h18 : (a + b) * (b - a) < b ^ 2 := by
          nlinarith
        have h19 : sqrt ((a + b) * (b - a)) < sqrt (b ^ 2) := by
          apply Real.sqrt_lt_sqrt
          nlinarith
          nlinarith
        have h20 : sqrt (b ^ 2) = b := by
          rw [Real.sqrt_sq (show b ≥ 0 by linarith)]
        have h21 : sqrt ((a + b) * (b - a)) < b := by
          nlinarith [h19, h20]
        linarith
      nlinarith [Real.sqrt_nonneg ((a + b) * (b - a)), Real.sq_sqrt (show (0 : ℝ) ≤ (a + b) * (b - a) by nlinarith)]
    nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg (b - a), Real.sqrt_nonneg b, Real.sq_sqrt (show (0 : ℝ) ≤ a + b by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b - a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith)]
  have h4 : sqrt (a + b) - sqrt b < sqrt b - sqrt (b - a) := by
    linarith [h1, Real.sqrt_nonneg (a + b), Real.sqrt_nonneg (b - a), Real.sqrt_nonneg b]
  linarith [h4]
  all_goals linarith
  <;> try { nlinarith }
  <;> try { norm_num }
  <;> try { nlinarith }