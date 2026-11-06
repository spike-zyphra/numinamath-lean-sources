import Mathlib

theorem algebra_2379 (z : ℂ) (hz : z.re = (z ^ 2).re ∧ z.im = -(z ^ 2).im) :
    z = 0 ∨ z = 1 ∨ z = -1 / 2 + Real.sqrt 3 / 2 * .I ∨ z = -1 / 2 - Real.sqrt 3 / 2 * .I := by 
  have hzre : z.re = (z ^ 2).re := hz.1
  have hzim : z.im = -(z ^ 2).im := hz.2

  simp [pow_two, Complex.ext_iff] at hzre hzim
  have eq1 := hzre
  have eq2 := hzim
  
  have eq3 : z.im * (1 + 2 * z.re) = 0 := by
    nlinarith
  
  cases' (mul_eq_zero.mp eq3) with him h2
  
  · 
    have h1 : z.im = 0 := by 
      linarith
  
    have eq4 : z.re * (z.re - 1) = 0 := by 
      nlinarith
  
    cases' (mul_eq_zero.mp eq4) with hre hre
  
    · 
      have hk : z.re = 0 := by 
        linarith
  
      have hz0 : z = 0 := by 
        simp [Complex.ext_iff, hk, h1]
  
      left
      exact hz0
  
    · 
      have hk : z.re = 1 := by 
        linarith
  
      have hz1 : z = 1 := by 
        simp [Complex.ext_iff, hk, h1]
  
      right
      left
      exact hz1
  
  · 
    have hk2 : z.re = -1 / 2 := by 
      linarith
  
    have eq5 : z.im ^ 2 = 3 / 4 := by 
      nlinarith [sq_nonneg (z.re), sq_nonneg (z.im)]
  
    have h10 : z.im = Real.sqrt 3 / 2 ∨ z.im = -Real.sqrt 3 / 2 := by 
      have h2 : z.im ^ 2 - 3 / 4 = 0 := by 
        linarith [eq5]
  
      have h3 : (z.im - Real.sqrt 3 / 2) * (z.im + Real.sqrt 3 / 2) = 0 := by 
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
      cases' (mul_eq_zero.mp h3) with h4 h5
  
      · 
        have hk : z.im = Real.sqrt 3 / 2 := by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
        left
        exact hk
  
      · 
        have hk : z.im = -Real.sqrt 3 / 2 := by 
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
  
        right
        exact hk
  
    cases h10 with 
    | inl him1 =>
      have hk2a : z.re = -1/2 := hk2
      have hk2b : z.im = Real.sqrt 3 / 2 := him1
  
      have hz2 : z = -1/2 + Real.sqrt 3 / 2 * Complex.I := by 
        simp [Complex.ext_iff, hk2a, hk2b]
  
      right
      right
      left
      exact hz2
  
    | inr him2 =>
      have hk2a : z.re = -1/2 := hk2
      have hk2b : z.im = -Real.sqrt 3 / 2 := him2
  
      have hz3 : z = -1/2 - Real.sqrt 3 / 2 * Complex.I := by 
        simp [Complex.ext_iff, hk2a, hk2b]
        <;> ring_nf <;> norm_num
  
      right
      right
      right
      exact hz3