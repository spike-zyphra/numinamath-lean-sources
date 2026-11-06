import Mathlib

theorem algebra_262353 (p q k : ℝ) (hk : k ≠ 0) :
    
    (∀  x : ℂ, x^2 + px + q = 0 ∧ x.im  = 0) → 
    
    (∀ y : ℂ, y^2 + (k + 1 / k) * p * y + p^2 + q * (k - 1 / k)^2 = 0 → y.im  = 0) ∧ 
    (∃ y1 y2 : ℝ, 
      y1^2 + (k + 1/k) * p * y1 + p^2 + q * (k - 1/k)^2 = 0 ∧ 
      y2^2 + (k + 1/k) * p * y2 + p^2 + q * (k - 1/k)^2 = 0 ∧ 
      
      ∀ z : ℂ, z^2 - y1z + q = 0 ∧ z^2 - y2z + q = 0 → z.im = 0) ∧ 
    { y | ∀ x1 x2 : ℝ, x1^2 + p * x1 + q = 0 ∧ x2^2 + p * x2 + q = 0 ∧ y^2 + (k + 1/k) * p * y + p^2 + q * (k - 1/k)^2 = 0 } = { k * x1 + (1/k) * x2, k * x2 + (1/k) * x1 } ∧
    { z | ∀ x1 x2 : ℝ, x1^2 + p * x1 + q = 0 ∧ x2^2 + p * x2 + q = 0 ∧ z^2 - (k * x1 + (1/k) * x2) * z + q = 0 } = 
      { ((k * x1 + (1/k) * x2) + (k * x2 + (1/k) * x1)) / 2, 
        ((k * x1 + (1/k) * x2) - (k * x2 + (1/k) * x1)) / 2 } := by
  intro hb1
  have h1 := hb1 1
  have h2 := hb1 0
  have h1' := hb1 2
  have h3 := hb1 (1 + Complex.I)
  have h4 := hb1 (1 - Complex.I)
  norm_num [Complex.ext_iff, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im] at h1 h2 h1' h3 h4
  all_goals 
    try { 
      nlinarith 
    }