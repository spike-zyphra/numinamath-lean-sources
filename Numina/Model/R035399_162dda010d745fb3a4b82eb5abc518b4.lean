import Mathlib

theorem algebra_21962 {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (h1 : (x + y)^2 + (x - y)^2 = 10) (h2 : (x + y)^4 + (x - y)^4 = 98) :
    x * y = Real.sqrt 6 := by 
  have h3 : x ^ 2 + y ^ 2 = 5 := by 
    nlinarith 
  have h4 : ((x + y) * (x - y)) ^ 2 = 1 := by 
    nlinarith [sq_nonneg ((x + y) ^ 2 - (x - y) ^ 2), sq_nonneg ((x + y) * (x - y)), h3]
  have h5 : (x + y) * (x - y) = 1 ∨ (x + y) * (x - y) = -1 := by 
    have h6 : ((x + y) * (x - y)) ^ 2 = 1 := h4
    have : (x + y) * (x - y) = 1 ∨ (x + y) * (x - y) = -1 := by 
      rw [sq_eq_one_iff] at h6 
      tauto 
    tauto 
  rcases h5 with h6 | h7 
  · -- Case $\left( x + y \right) \cdot \left( x - y \right) = 1$, which means $x^2 - y^2 = 1$.
    have h7 : x ^ 2 - y ^ 2 = 1 := by 
      linarith 
    have hx2 : x ^ 2 = 3 := by 
      have h9 : x ^ 2 + y ^ 2 = 5 := h3 
      nlinarith 
    have hy2 : y ^ 2 = 2 := by 
      have h9 : x ^ 2 + y ^ 2 = 5 := h3 
      nlinarith 
    have h6' : (x * y) ^ 2 = 6 := by 
      nlinarith 
    have h8 : x * y = Real.sqrt 6 := by 
      have h9 : (x * y) ^ 2 = (6 : ℝ) := h6' 
      have h10 : 0 < (x * y : ℝ) := by 
        nlinarith 
      have h11 : Real.sqrt ((x * y) ^ 2) = Real.sqrt (6 : ℝ) := by 
        rw [h9] 
      have h12 : Real.sqrt ((x * y) ^ 2) = (x * y : ℝ) := by 
        rw [Real.sqrt_sq (show 0 ≤ (x * y : ℝ) by linarith)] 
      have h13 : (x * y : ℝ) = Real.sqrt (6 : ℝ) := by 
        linarith [h11, h12] 
      exact h13 
    exact h8 
  · -- Case $\left( x + y \right) \cdot \left( x - y \right) = -1$, which means $x^2 - y^2 = -1$.
    have h8' : x ^ 2 - y ^ 2 = -1 := by 
      linarith 
    have hx2 : x ^ 2 = 2 := by 
      nlinarith [h3, h8'] 
    have hy2 : y ^ 2 = 3 := by 
      nlinarith [h3, h8'] 
    have h6' : (x * y) ^ 2 = 6 := by 
      nlinarith 
    have h8 : x * y = Real.sqrt 6 := by 
      have h9 : (x * y) ^ 2 = (6 : ℝ) := h6' 
      have h10 : 0 < (x * y : ℝ) := by 
        nlinarith 
      have h11 : Real.sqrt ((x * y) ^ 2) = Real.sqrt (6 : ℝ) := by 
        rw [h9] 
      have h12 : Real.sqrt ((x * y) ^ 2) = (x * y : ℝ) := by 
        rw [Real.sqrt_sq (show 0 ≤ (x * y : ℝ) by linarith)]
      have h13 : (x * y : ℝ) = Real.sqrt (6 : ℝ) := by 
        linarith [h11, h12] 
      exact h13 
    exact h8