import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_204005 (f : ℝ → ℝ) (hf : f = λ x => (x+1)*(x+2)*(x+3)*(x+4) + 24)
  (a b : ℝ) (ha : a = -2) (hb : b = 2) :
  IsGreatest (image f (Icc a b)) 384 ∧ IsLeast (image f (Icc a b)) 23 := by 
  rw [ha, hb]
  constructor 
  · -- Show 384 is greatest in the image
    constructor 
    · -- Show 384 is in the image 
      use (2 : ℝ)
      constructor
      · -- Show 2 is in the interval 
        norm_num
      · -- Show f(2) = 384
        rw [hf]
        norm_num 
    · -- Show y in the image <= 384 
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [hf]
      simp at hx ⊢ 
      have h11 : (x + 1) * (x + 2) * (x + 3) * (x + 4) ≤ 360 := by 
        nlinarith [sq_nonneg (x ^ 2 + 5 * x + 5), sq_nonneg (x + 2.5), sq_nonneg (x ^ 2 + 5 * x - 14), 
          sq_nonneg (x - 2), sq_nonneg (x + 2), 
          sq_nonneg ((x + 2.5) ^ 2 - 2.5 ^ 2), 
          hx.1, hx.2, 
          mul_nonneg (show (0 : ℝ) ≤ (2 + x) by nlinarith) (show (0 : ℝ) ≤ (2 - x) by nlinarith)
        ]
      nlinarith 
  · -- Show 23 is the least in the image
    constructor 
    · -- Show 23 is in the image 
      use (-5 + Real.sqrt 5) / 2
      constructor 
      · -- Show the point is in the interval 
        have h1 : -2 ≤ (-5 + Real.sqrt 5) / 2 := by 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        have h2 : (-5 + Real.sqrt 5) / 2 ≤ 2 := by 
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
        exact ⟨h1, h2⟩ 
      · -- Show f(-5/2 + sqrt 5 / 2) = 23 
        rw [hf]
        have h3 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
        have h4 : Real.sqrt 5 ^ 4 = 25 := by
          calc 
            Real.sqrt 5 ^ 4 = (Real.sqrt 5 ^ 2) ^ 2 := by ring 
            _ = (5) ^ 2 := by rw [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
            _ = 25 := by norm_num 
        simp [h3, h4]
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    · -- Show any y in the image ≥ 23 
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      rw [hf]
      simp at hx ⊢
      nlinarith [sq_nonneg (x ^ 2 + 5 * x + 5), sq_nonneg (x + 2.5), sq_nonneg (x ^ 2 + 5 * x - 14), 
        sq_nonneg (x - 2), sq_nonneg (x + 2), 
        sq_nonneg ((x + 2.5) ^ 2 - 2.5 ^ 2), 
        hx.1, hx.2, 
        mul_nonneg (show (0 : ℝ) ≤ (2 + x) by nlinarith) (show (0 : ℝ) ≤ (2 - x) by nlinarith)
      ]