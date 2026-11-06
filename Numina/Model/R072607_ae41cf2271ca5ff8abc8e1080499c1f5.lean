import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_166846 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sqrt (4 * (sin x)^4 - 2 * cos (2 * x) + 3) +
    sqrt (4 * (cos x)^4 + 2 * cos (2 * x) + 3)) :
  ∀ x, f x = 4 := by
  intro x
  have h1 : f x = sqrt (4 * (sin x) ^ 4 - 2 * cos (2 * x) + 3) + sqrt (4 * (cos x) ^ 4 + 2 * cos (2 * x) + 3) := h₀ x
  have h2 : cos (2 * x) = 2 * (cos x) ^ 2 - 1 := by
    rw [cos_two_mul]
    <;> simp [mul_assoc]
  have h3 : 4 * (sin x) ^ 4 - 2 * cos (2 * x) + 3 = (2 * (cos x) ^ 2 - 3) ^ 2 := by
    rw [h2]
    have h4 : sin x ^ 2 = 1 - (cos x ^ 2) := by
      have h5 : sin x ^ 2 + (cos x ^ 2) = 1 := by
        exact Real.sin_sq_add_cos_sq x
      have h6 : sin x ^ 2 = 1 - (cos x ^ 2) := by
        linarith
      linarith
    have h4' : (sin x) ^ 4 = (1 - (cos x ^ 2)) ^ 2 := by
      have h7 : (sin x) ^ 4 = ((sin x) ^ 2) ^ 2 := by ring
      rw [h7, h4]
      <;> ring
    rw [h4']
    <;> ring
  have h5 : 4 * (cos x) ^ 4 + 2 * cos (2 * x) + 3 = (2 * (cos x) ^ 2 + 1) ^ 2 := by
    rw [h2]
    <;> ring
  have h7 : sqrt (4 * (sin x) ^ 4 - 2 * cos (2 * x) + 3) = abs (2 * (cos x) ^ 2 - 3) := by
    rw [h3]
    have h8 : sqrt ((2 * (cos x) ^ 2 - 3 : ℝ) ^ 2) = abs (2 * (cos x) ^ 2 - 3) := by
      rw [Real.sqrt_sq_eq_abs]
    exact h8
  have h8 : sqrt (4 * (cos x) ^ 4 + 2 * cos (2 * x) + 3) = 2 * (cos x) ^ 2 + 1 := by
    rw [h5]
    have h9 : sqrt ((2 * (cos x) ^ 2 + 1 : ℝ) ^ 2) = (2 * (cos x) ^ 2 + 1) := by
      rw [Real.sqrt_sq (by positivity)]
      <;> nlinarith [Real.sin_sq_add_cos_sq x]
    exact h9
  rw [h7, h8] at h1
  have hcos1 : 2 * (cos x) ^ 2 ≤ (2 : ℝ) := by
    nlinarith [Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq x, sq_nonneg (cos x ^ 2 - 1)]
  have hcos2 : (2 * (cos x) ^ 2 - 3 : ℝ) ≤ 0 := by
    nlinarith
  have h11 : abs (2 * (cos x) ^ 2 - 3) = (3 - 2 * (cos x) ^ 2 : ℝ) := by
    have h12 : 2 * (cos x) ^ 2 - 3 ≤ 0 := hcos2
    rw [abs_of_nonpos h12]
    <;> linarith
  rw [h11] at h1
  rw [h1]
  <;> ring_nf <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (2 * (cos x) ^ 2 - 3), sq_nonneg (2 * (cos x) ^ 2 - 1), Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq x, Real.sin_sq_add_cos_sq x]