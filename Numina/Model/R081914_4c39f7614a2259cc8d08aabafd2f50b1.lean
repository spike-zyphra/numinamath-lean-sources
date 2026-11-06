import Mathlib

open Real

variable {a b c : ℝ}

def f_92 (a b c x : ℝ) : ℝ :=
  b * x ^ 2 + c * x - a

theorem algebra_92 (a b c : ℝ) (h₀ : a + b = 8) (h₁ : a * b - c ^ 2 + 8 * √2 * c = 48) :
  f_92 a b c ((-√2 + √6) / 2) = 0 ∧ f_92 a b c ((-√2 - √6) / 2) = 0 := by
  have h2 : b = 8 - a := by linarith
  rw [h2] at h₁
  have h3 : (a - 4) ^ 2 + (c - 4 * √2) ^ 2 = 0 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 2 from by norm_num), Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (6 : ℝ) from by norm_num)]
  have ha1 : a - 4 = 0 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * √2)]
  have ha : a = 4 := by linarith
  have hc1 : c - 4 * √2 = 0 := by
    nlinarith [sq_nonneg (a - 4), sq_nonneg (c - 4 * √2)]
  have hc : c = 4 * √2 := by linarith
  have hb : b = 4 := by
    linarith [h₀, ha]
  constructor
  · -- Show that (-√2 + √6) / 2 is a root
    rw [show a = 4 by linarith [ha], show b = 4 by linarith [hb], show c = 4 * √2 by linarith [hc]]
    simp [f_92]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]
  · -- Show that (-√2 - √6) / 2 is a root
    rw [show a = 4 by linarith [ha], show b = 4 by linarith [hb], show c = 4 * √2 by linarith [hc]]
    simp [f_92]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 6, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.mul_self_sqrt (show 0 ≤ (6 : ℝ) by norm_num)]