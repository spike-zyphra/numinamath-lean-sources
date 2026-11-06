import Mathlib

open Real Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_22691 (θ : ℝ) (h : Real.tan θ = 2) :
    (exp (2 * I * θ) - 1) / (exp (2 * I * θ) + 1) = 2 * I := by
  have h1 : Real.cos θ ≠ 0 := by
    by_contra h1
    have : Real.tan θ = 0 := by
      rw [Real.tan_eq_sin_div_cos]
      simp [h1]
    rw [this] at h
    norm_num at h
  have h2 : Real.sin θ = 2 * Real.cos θ := by
    have h3 : Real.tan θ = Real.sin θ / Real.cos θ := by
      rw [Real.tan_eq_sin_div_cos]
    rw [h3] at h
    field_simp [h1] at h ⊢
    linarith
  have h3 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h4 : Real.sin θ ^ 2 = 4 * Real.cos θ ^ 2 := by
    rw [h2]
    nlinarith
  have h5 : Real.cos θ ^ 2 = 1 / 5 := by
    nlinarith
  have h6 : Real.sin θ ^ 2 = 4 / 5 := by
    nlinarith
  have h7 : exp (2 * I * θ) = -3 / 5 + 4 / 5 * I := by
    simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
    have h7 : Real.cos (2 * θ) = -3 / 5 := by
      have h7 : Real.cos (2 * θ) = 2 * Real.cos θ ^ 2 - 1 := Real.cos_two_mul θ
      rw [h7]
      nlinarith [h5]
    have h8 : Real.sin (2 * θ) = 4 / 5 := by
      have h8 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
      rw [h8, h2]
      nlinarith [h5]
    constructor <;> try linarith [h7, h8]
  rw [h7]
  field_simp [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq]
  all_goals norm_num