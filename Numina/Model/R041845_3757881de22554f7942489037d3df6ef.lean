import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_280506 {A ω φ : ℝ} (hA : A ≠ 0) (hω : ω > 0)
  (hφ : 0 < φ ∧ φ < π / 2) (f : ℝ → ℝ) (hf : f = λ x => A * sin (ω * x + φ))
  (h : f (5 * π / 6) + f 0 = 0) :
  ω ≥ 6 / 5 := by
  rw [hf] at h
  simp at h
  have h1 : A * sin (ω * (5 * π / 6) + φ) + A * sin φ = 0 := by
    simpa using h
  have h2 : A ≠ 0 := hA
  have h3 : sin (ω * (5 * π / 6) + φ) + sin φ = 0 := by
    apply (mul_left_inj' h2).mp
    linarith
  have h5 : sin (ω * (5 * π / 6) + φ) = - sin φ := by linarith
  have h6 : 0 < φ := hφ.left
  have h7 : φ < π / 2 := hφ.right
  have h8 : 0 < sin φ := by
    apply sin_pos_of_pos_of_lt_pi
    · linarith
    · linarith [Real.pi_pos]
  by_contra h10
  push_neg at h10
  have h13 : 0 < ω * (5 * π / 6) := by
    nlinarith [Real.pi_pos, hω]
  have h14 : ω * (5 * π / 6) < π := by
    nlinarith [h10, Real.pi_pos]
  -- Expanding using the addition formula:
  have h5b : sin (ω * (5 * π / 6) + φ) = sin (ω * (5 * π / 6)) * cos φ + cos (ω * (5 * π / 6)) * sin φ := by
    rw [sin_add]
  rw [h5b] at h5
  have h5c : sin (ω * (5 * π / 6)) > 0 := by
    apply sin_pos_of_pos_of_lt_pi
    · nlinarith [Real.pi_pos, h13]
    · nlinarith [Real.pi_pos, h14]
  have hcos1 : cos (ω * (5 * π / 6)) > -1 := by
    have hcos2 : cos (ω * (5 * π / 6)) > cos (π) := by
      apply Real.cos_lt_cos_of_nonneg_of_le_pi
      all_goals
      nlinarith [Real.pi_pos, h13, h14]
    have hcos3 : cos (π) = -1 := Real.cos_pi
    linarith
  -- From h5: sin (ω * (5 * π / 6)) * cos φ + cos (ω * (5 * π / 6)) * sin φ = - sin φ.
  have hcos3 : cos φ > 0 := by
    have h8 : 0 < φ := hφ.left
    have h9 : φ < π / 2 := hφ.right
    have h10 : cos φ > 0 := by
      apply cos_pos_of_mem_Ioo
      constructor
      · 
        linarith [h8]
      · 
        linarith [h9]
    linarith
  have h10a : sin (ω * (5 * π / 6)) * cos φ > 0 := by
    apply mul_pos
    · linarith [h5c]
    · linarith [hcos3]
  have h11a : cos (ω * (5 * π / 6)) + 1 > 0 := by
    nlinarith [hcos1, Real.pi_pos]
  have h12a : sin (ω * (5 * π / 6)) * cos φ + sin φ * (cos (ω * (5 * π / 6)) + 1) = 0 := by
    linarith [h5, hcos1]
  nlinarith [h12a, h10a, h11a, h8, hcos3, h5c, hcos1]