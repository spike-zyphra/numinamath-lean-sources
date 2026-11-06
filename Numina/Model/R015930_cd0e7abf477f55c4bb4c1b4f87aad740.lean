import Mathlib

theorem algebra_161388 (p q : ℝ) (h₀ : 0 ≤ p) (h₁ : 0 ≤ q)
    (h₂ : 25 * p^2 - q^2 ≥ 0) :
    Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) -
    Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) =
    2 * Real.sqrt (5 * p - q) := by 
  have h3 : 0 ≤ 5 * p - q := by
    nlinarith [sq_nonneg (5 * p - q), sq_nonneg (5 * p + q), h₀, h₁, h₂]
  have h4 : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) ≥ 0 := by positivity
  have h5 : Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ≥ 0 := by positivity
  have h6 : 0 ≤ (5 * p - q : ℝ) := h3
  have h7 : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 = 10 * p + 2 * Real.sqrt (25 * p^2 - q^2) := by
    rw [Real.sq_sqrt]
    nlinarith [Real.sqrt_nonneg (25 * p^2 - q^2), h₀, h₁, h₂, sq_nonneg (Real.sqrt (25 * p^2 - q^2)), sq_nonneg (5 * p - q)]
  -- We need to show 10 * p - 2 * Real.sqrt (25 * p^2 - q^2) ≥ 0
  have h11 : 0 ≤ 10 * p - 2 * Real.sqrt (25 * p^2 - q^2) := by
    have h12 : Real.sqrt (25 * p^2 - q^2) ≤ 5 * p := by
      have h13 : Real.sqrt (25 * p^2 - q^2) ^ 2 ≤ (5 * p) ^ 2 := by
        have h14 : Real.sqrt (25 * p^2 - q^2) ^ 2 = 25 * p^2 - q^2 := by 
          rw [Real.sq_sqrt]
          linarith
        have h15 : (5 * p) ^ 2 = 25 * p^2 := by ring
        nlinarith [h14, h15, sq_nonneg (q), h₀, h₁]
      have h14 : Real.sqrt (25 * p^2 - q^2) ≥ 0 := Real.sqrt_nonneg (25 * p^2 - q^2)
      have h15 : (5 * p) ≥ 0 := by linarith
      nlinarith [Real.sqrt_nonneg (25 * p^2 - q^2), show 0 ≤ (5 * p : ℝ) by nlinarith, h13]
    linarith [h12]
  have h8 : Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 = 10 * p - 2 * Real.sqrt (25 * p^2 - q^2) := by
    rw [Real.sq_sqrt]
    linarith [h11]
  have h9 : Real.sqrt (5 * p - q) ^ 2 = 5 * p - q := by 
    rw [Real.sq_sqrt]
    linarith
  have eq1 : (Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) - Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ) ^ 2 = (2 * Real.sqrt (5 * p - q) ) ^ 2 := by
    have h7' : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 = 10 * p + 2 * Real.sqrt (25 * p^2 - q^2) := h7
    have h8' : Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 = 10 * p - 2 * Real.sqrt (25 * p^2 - q^2) := h8
    have h10 : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) * Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) = 2 * q := by
      have h11 : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) * Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) =
          Real.sqrt ((10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) * (10 * p - 2 * Real.sqrt (25 * p^2 - q^2))) := by 
        rw [← Real.sqrt_mul (by
          nlinarith [Real.sqrt_nonneg (25 * p^2 - q^2), h₀, h₁, h₂, sq_nonneg (Real.sqrt (25 * p^2 - q^2)), sq_nonneg (5 * p - q)]
        )]
        all_goals norm_num
        all_goals nlinarith 
      rw [h11]
      have h12 : (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) * (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) = (4 * q^2) := by
        nlinarith [Real.sqrt_nonneg (25 * p^2 - q^2), Real.sq_sqrt (show (25 * p^2 - q^2 : ℝ) ≥ 0 by linarith), sq_nonneg (Real.sqrt (25 * p^2 - q^2)), sq_nonneg (5 * p - q), h3]
      rw [h12]
      have h13 : Real.sqrt (4 * q ^ 2) = 2 * q := by
        have h17 : 4 * q ^ 2 = (2 * q) ^ 2 := by ring
        rw [h17]
        rw [Real.sqrt_sq (by linarith)]
      rw [h13]
    rw [show (Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) - Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2))) ^ 2 
        = Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 + Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ^ 2 - 2 * (Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) * Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2))) by ring]
    rw [h7', h8', h10]
    have h15 : (2 * Real.sqrt (5 * p - q)) ^ 2 = 20 * p - 4 * q := by
      calc
        (2 * Real.sqrt (5 * p - q)) ^ 2 = 4 * (Real.sqrt (5 * p - q) ^ 2) := by ring
        _ = 4 * (5 * p - q) := by rw [Real.sq_sqrt (by linarith)]
        _ = 20 * p - 4 * q := by ring
    nlinarith [h15]
  have eq2 : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) - Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) ≥ 0 := by
    have h7' : Real.sqrt (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)) ≥ Real.sqrt (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)) := by
      apply Real.sqrt_le_sqrt
      nlinarith [Real.sqrt_nonneg (25 * p^2 - q^2), Real.sq_sqrt (show (25 * p^2 - q^2 : ℝ) ≥ 0 by linarith), sq_nonneg (Real.sqrt (25 * p^2 - q^2)), h3, Real.sqrt_nonneg (5 * p - q), sq_nonneg (5 * p - q)]
    linarith
  have eq3 : 2 * Real.sqrt (5 * p - q) ≥ 0 := by positivity
  nlinarith [eq1, eq2, eq3, Real.sqrt_nonneg (10 * p + 2 * Real.sqrt (25 * p^2 - q^2)), Real.sqrt_nonneg (10 * p - 2 * Real.sqrt (25 * p^2 - q^2)), Real.sqrt_nonneg (5 * p - q)]