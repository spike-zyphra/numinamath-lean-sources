import Mathlib

theorem calculus_22115 {a b : ℂ} (ha : a = 5 - 8 * .I) (hb : b = 30 + 48 * .I) :
    Complex.abs (a * b) = 534 := by
  rw [ha, hb]
  have h1 : (5 - 8 * Complex.I : ℂ) * (30 + 48 * Complex.I) = (534 : ℂ) := by 
    simp [Complex.ext_iff, Complex.I_mul_I, mul_add, sub_mul, mul_assoc]
    all_goals norm_num
  rw [h1]
  simp [Complex.abs, Complex.normSq]
  all_goals norm_num
  all_goals ring_nf <;> norm_num