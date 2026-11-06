import Mathlib

open Real Set
open scoped Real

theorem inequalities_272898 (x : ℝ) :
  -sqrt 2 ≤ sin x + cos x ∧ sin x + cos x ≤ sqrt 2 ∧
  -sqrt 2 ≤ sin x - cos x ∧ sin x - cos x ≤ sqrt 2 ∧
  1 ≤ abs (sin x) + abs (cos x) ∧ abs (sin x) + abs (cos x) ≤ sqrt 2 := by
  have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : -sqrt 2 ≤ sin x + cos x := by
    have h3_sq : (sin x + cos x) ^ 2 ≤ (2 : ℝ) := by
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h3 : -Real.sqrt 2 ≤ sin x + cos x := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin x + cos x), sq_nonneg (sin x + cos x + Real.sqrt 2)]
    exact h3
  have h3 : sin x + cos x ≤ sqrt 2 := by
    have h4_sq : (sin x + cos x) ^ 2 ≤ (2 : ℝ) := by
      nlinarith [sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : sin x + cos x ≤ Real.sqrt 2 := by
      have h6 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      nlinarith [Real.sqrt_nonneg 2, sq_nonneg (sin x + cos x), h6, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h5
  have h4 : -sqrt 2 ≤ sin x - cos x := by
    have hhtmp : (sin x - cos x) ^ 2 ≤ (2 : ℝ) := by
      nlinarith [sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h5 : -Real.sqrt 2 ≤ sin x - cos x := by
      nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin x - cos x), sq_nonneg (sin x - cos x + Real.sqrt 2)]
    exact h5
  have h5 : sin x - cos x ≤ sqrt 2 := by
    have hhtmp2 : (sin x - cos x) ^ 2 ≤ (2 : ℝ) := by
      nlinarith [sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h6 : sin x - cos x ≤ Real.sqrt 2 := by
      have h7 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt]
        norm_num
      nlinarith [Real.sqrt_nonneg 2, sq_nonneg (sin x - cos x), h7, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    exact h6
  have h7 : 1 ≤ abs (sin x) + abs (cos x) := by
    have h_abs_sq_ge_1 : (abs (sin x) + abs (cos x)) ^ 2 ≥ (1 : ℝ) := by
      have h126 : (abs (sin x) + abs (cos x)) ^ 2 = (abs (sin x)) ^ 2 + (abs (cos x)) ^ 2 + 2 * (abs (sin x) * abs (cos x)) := by ring
      rw [h126]
      have h127 : (abs (sin x)) ^ 2 = (sin x ) ^ 2 := by simp [abs_pow]
      have h128 : (abs (cos x)) ^ 2 = (cos x ) ^ 2 := by simp [abs_pow]
      rw [h127, h128]
      nlinarith [sq_nonneg (abs (sin x) - abs (cos x)), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, abs_nonneg (sin x), abs_nonneg (cos x), mul_nonneg (abs_nonneg (sin x)) (abs_nonneg (cos x))]
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sqrt_nonneg 2, sq_nonneg (abs (sin x) + abs (cos x)), h_abs_sq_ge_1, abs_nonneg (sin x), abs_nonneg (cos x)]
  have h8 : abs (sin x) + abs (cos x) ≤ sqrt 2 := by
    have h115 : (abs (sin x) + abs (cos x)) ^ 2 ≤ (2 : ℝ) := by
      have h67 : (abs (sin x) + abs (cos x)) ^ 2 = (abs (sin x)) ^ 2 + (abs (cos x)) ^ 2 + 2 * (abs (sin x) * abs (cos x)) := by ring
      rw [h67]
      have h98 : (abs (sin x)) ^ 2 = (sin x ) ^ 2 := by simp [abs_pow]
      have h100 : (abs (cos x)) ^ 2 = (cos x ) ^ 2 := by simp [abs_pow]
      rw [h98, h100]
      nlinarith [sq_nonneg (abs (sin x) - abs (cos x)), sq_nonneg (sin x ^ 2 - cos x ^ 2), Real.sin_sq_add_cos_sq x, abs_nonneg (sin x), abs_nonneg (cos x), mul_nonneg (abs_nonneg (sin x)) (abs_nonneg (cos x)), sq_nonneg (sin x), sq_nonneg (cos x)]
    have h7' : abs (sin x) + abs (cos x) ≤ Real.sqrt 2 := by
      nlinarith [Real.sqrt_nonneg 2, h115, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (abs (sin x) + abs (cos x) - Real.sqrt 2)]
    exact h7'
  constructor
  · -- Prove -Real.sqrt 2 ≤ sin x + cos x
    exact h2
  constructor
  · -- Prove sin x + cos x ≤ Real.sqrt 2
    exact h3
  constructor
  · -- Prove -Real.sqrt 2 ≤ sin x - cos x
    exact h4
  constructor
  · -- Prove sin x - cos x ≤ Real.sqrt 2
    exact h5
  constructor
  · -- Prove 1 ≤ abs (sin x) + abs (cos x)
    exact h7
  · -- Prove abs (sin x) + abs (cos x) ≤ Real.sqrt 2
    exact h8