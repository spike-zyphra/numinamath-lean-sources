import Mathlib

open Real Set
open scoped Real

theorem algebra_13078 (θ : Real) (hθ : θ ∈ Icc (π / 4) (π / 2)) (h : sin θ + cos θ = 4 * sqrt 2 / sqrt 17) :
    cos (2 * θ) = -8 / 17 := by 
  rcases hθ with ⟨h5, h6⟩
  have h1 : (sin θ + cos θ) ^ 2 = (4 * Real.sqrt 2 / Real.sqrt 17) ^ 2 := by 
    rw [h]
  have eq1 : (sin θ + cos θ) ^ 2 = (32 / 17 : ℝ) := by
    have eq2 : (4 * Real.sqrt 2 / Real.sqrt 17) ^ 2 = (32 / 17 : ℝ) := by
      have h2 : Real.sqrt 17 > 0 := by positivity
      have h3 : Real.sqrt 2 > 0 := by positivity
      field_simp
      <;> ring_nf <;> norm_num [Real.sq_sqrt]
      <;> linarith [Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
    nlinarith [h1, eq2]
  have eq3 : sin θ * cos θ = (15 / 34 : ℝ) := by
    have eq4 : (sin θ + cos θ) ^ 2 = (32 / 17 : ℝ) := eq1
    have eq4a : (sin θ + cos θ) ^ 2 = (sin θ) ^ 2 + (cos θ) ^ 2 + 2 * (sin θ * cos θ) := by 
      ring
    rw [eq4a] at eq4
    have eq5 : (sin θ) ^ 2 + (cos θ) ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    nlinarith
  have eq4 : (sin θ - cos θ) ^ 2 = (2 / 17 : ℝ) := by 
    nlinarith [Real.sin_sq_add_cos_sq θ, eq3]
  -- θ ∈ [π/4, π/2] implies sin θ ≥ cos θ
  have h3 : sin θ ≥ cos θ := by
    have h4 : sin θ ≥ sin (π / 4) := by 
      apply Real.sin_le_sin_of_le_of_le_pi_div_two
      all_goals linarith [Real.pi_pos]
    have h5a : sin (π / 4) = Real.sqrt 2 / 2 := by
      rw [Real.sin_pi_div_four]
    have h6a : cos θ ≤ cos (π / 4) := by 
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      all_goals linarith [Real.pi_pos]
    have h7a : cos (π / 4) = Real.sqrt 2 / 2 := by
      rw [Real.cos_pi_div_four]
    have h8a : sin θ ≥ cos θ := by
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    linarith
  -- From sin θ ≥ cos θ, we know that cos θ - sin θ ≤ 0
  have eq5a : cos θ - sin θ ≤ 0 := by 
    linarith [h3]
  have eq6 : cos θ - sin θ = -Real.sqrt (2 / 17 : ℝ) := by
    have eq7 : (cos θ - sin θ) ^ 2 = (2 / 17 : ℝ) := by 
      nlinarith 
    have eq8 : Real.sqrt ((cos θ - sin θ) ^ 2) = |cos θ - sin θ| := by 
      rw [Real.sqrt_sq_eq_abs]
    have eq9 : |cos θ - sin θ| = Real.sqrt (2 / 17 : ℝ) := by
      have eq10 : |cos θ - sin θ| = Real.sqrt ((cos θ - sin θ) ^ 2) := by 
        rw [eq8]
      rw [eq10]
      rw [eq7]
    have h6a : cos θ - sin θ ≤ 0 := eq5a
    have eq11 : cos θ - sin θ = - Real.sqrt (2 / 17 : ℝ) := by 
      cases' abs_cases (cos θ - sin θ) with h12 h12
      · -- case cos θ - sin θ ≥ 0
        nlinarith [eq9, h6a]
      · -- case cos θ - sin θ < 0
        nlinarith [eq9]
    linarith
  have eq7a : cos (2 * θ) = (cos θ) ^ 2 - (sin θ) ^ 2 := by
    rw [cos_two_mul, Real.cos_sq, Real.sin_sq]
    <;> ring_nf <;> simp [Real.sin_sq, Real.cos_sq]
    <;> ring
  rw [eq7a]
  have eq8a : (cos θ) ^ 2 - (sin θ) ^ 2 = (cos θ - sin θ) * (cos θ + sin θ) := by
    ring
  rw [eq8a]
  rw [show cos θ + sin θ = (4 * Real.sqrt 2 / Real.sqrt 17 : ℝ) by linarith [h], eq6]
  field_simp
  <;> ring_nf
  <;> norm_num [Real.sq_sqrt]
  <;> linarith [Real.sq_sqrt (show 0 ≤ (17 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
  all_goals linarith