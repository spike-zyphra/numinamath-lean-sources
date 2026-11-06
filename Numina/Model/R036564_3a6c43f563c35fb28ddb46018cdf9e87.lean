import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_120946 (a b : ℝ) (ha : 1 ≤ a ∧ a ≤ sqrt 3) (hb : 1 ≤ b ∧ b ≤ sqrt 3) :
    (a^2 + b^2 - 1) / (a * b) ∈ Icc 1 (sqrt 3) := by
  have h1 : 1 ≤ a := ha.1
  have h2 : a ≤ sqrt 3 := ha.2
  have h3 : 1 ≤ b := hb.1
  have h4 : b ≤ sqrt 3 := hb.2
  have h5 : 0 < a * b := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h7 : a ^ 2 + b ^ 2 - 1 ≥ a * b := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1), 
      Real.sqrt_nonneg 3, 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    ]
  have h8 : a ^ 2 + b ^ 2 - 1 ≤ sqrt 3 * (a * b) := by 
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - sqrt 3), sq_nonneg (b - sqrt 3), 
      sq_nonneg (a * b - (a * b)), 
      Real.sqrt_nonneg 3, 
      mul_nonneg (show 0 ≤ a - 1 by nlinarith) (show 0 ≤ b - 1 by nlinarith), 
      mul_nonneg (show 0 ≤ sqrt 3 - a by
        nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        ) (show 0 ≤ sqrt 3 - b by
          nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
        ), 
      h1, h3, 
      sq_nonneg (a * b), 
      sq_nonneg (sqrt 3), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
      mul_nonneg (show 0 ≤ a by nlinarith) (show 0 ≤ b by nlinarith)
    ]
  have h9 : 1 ≤ (a^2 + b^2 - 1) / (a * b) := by 
    apply (le_div_iff₀ (by positivity)).mpr 
    linarith 
  have h10 : (a^2 + b^2 - 1) / (a * b) ≤ sqrt 3 := by 
    apply (div_le_iff₀ (by positivity)).mpr 
    nlinarith 
  constructor 
  · -- Show that 1 ≤ $\frac{a^2 + b^2 - 1}{a * b}$ 
    linarith [h9] 
  · -- Show that $\frac{a^2 + b^2 - 1}{a * b}$ ≤ sqrt 3 
    linarith [h10]