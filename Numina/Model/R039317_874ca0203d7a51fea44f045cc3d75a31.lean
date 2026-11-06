import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_119026 {f g : ℝ → ℝ}
  (hf : ∀ x, f x = sin (π/4 * x - π/6) - 2 * (cos (π/8 * x))^2 + 1)
  (hg : ∀ x, g (1 + x) = f (1 - x)) :
  IsGreatest (image g (Icc 0 (4/3))) (Real.sqrt 3 / 2) := by
  have h1 : ∀ x, g x = f (2 - x) := by
    intro x
    have h1 := hg (x - 1)
    rw [show 1 + (x - 1) = x by ring, show 1 - (x - 1) = 2 - x by ring] at h1
    linarith

  have h2 : ∀ x, g x = Real.sqrt 3 / 2 * Real.cos (Real.pi / 4 * x) - 3 / 2 * Real.sin (Real.pi / 4 * x) := by
    intro x
    rw [h1 x]
    have hf2 : f (2 - x) = Real.sin (Real.pi / 4 * (2 - x) - Real.pi / 6) - 2 * (Real.cos (Real.pi / 8 * (2 - x))) ^ 2 + 1 := by
      specialize hf (2 - x)
      simpa using hf
    rw [hf2]
    have h3 : Real.pi / 4 * (2 - x) - Real.pi / 6 = Real.pi / 3 - Real.pi / 4 * x := by
      ring_nf
    have h4 : Real.pi / 8 * (2 - x) = Real.pi / 4 - Real.pi / 8 * x := by
      ring_nf
    rw [h3, h4]
    have h5 : 2 * (Real.cos (Real.pi / 4 - Real.pi / 8 * x)) ^ 2 = 1 + Real.sin (Real.pi / 4 * x) := by
      have h7 : 2 * (Real.cos (Real.pi / 4 - Real.pi / 8 * x)) ^ 2 = 1 + Real.cos (2 * (Real.pi / 4 - Real.pi / 8 * x)) := by
        have h8 : 2 * Real.cos (Real.pi / 4 - Real.pi / 8 * x) ^ 2 = 1 + Real.cos (2 * (Real.pi / 4 - Real.pi / 8 * x)) := by
          rw [Real.cos_two_mul]
          all_goals ring
        linarith
      have h9 : 2 * (Real.pi / 4 - Real.pi / 8 * x) = Real.pi / 2 - Real.pi / 4 * x := by
        ring_nf
      rw [h9] at h7
      have h10 : Real.cos (Real.pi / 2 - Real.pi / 4 * x) = Real.sin (Real.pi / 4 * x) := by
        rw [Real.cos_pi_div_two_sub]
      rw [h10] at h7
      linarith
    rw [h5]
    have h6 : Real.sin (Real.pi / 3 - Real.pi / 4 * x) = Real.sin (Real.pi / 3) * Real.cos (Real.pi / 4 * x) - Real.cos (Real.pi / 3) * Real.sin (Real.pi / 4 * x) := by
      rw [Real.sin_sub]
    rw [h6]
    have h7 : Real.sin (Real.pi / 3) = Real.sqrt 3 / 2 := by
      rw [Real.sin_pi_div_three]
    have h8 : Real.cos (Real.pi / 3) = 1 / 2 := by
      rw [Real.cos_pi_div_three]
    rw [h7, h8]
    ring_nf
  constructor
  · -- Show sqrt 3 / 2 is in the image of g over [0, 4/3].
    use 0
    constructor
    · -- Show 0 is in [0, 4/3].
      norm_num
    · -- Show g 0 = sqrt 3 / 2.
      have h7 : g 0 = Real.sqrt 3 / 2 := by
        rw [h2 0]
        norm_num [Real.sin_zero, Real.cos_zero]
      linarith
  · -- Show sqrt 3 / 2 is the greatest element in the image.
    intro y
    rintro ⟨x, hx, h_eq⟩
    rw [mem_Icc] at hx
    have h3 : x ≥ 0 := by linarith
    have h4 : x ≤ 4 / 3 := by linarith
    rw [h2 x] at h_eq
    have h5 : Real.pi / 4 * x ≥ 0 := by
      nlinarith [Real.pi_pos]
    have h6 : Real.pi / 4 * x ≤ Real.pi / 3 := by
      nlinarith [Real.pi_pos, mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ (4 : ℝ) by norm_num)]
    have h7 : Real.sin (Real.pi / 4 * x) ≥ 0 := by
      apply Real.sin_nonneg_of_nonneg_of_le_pi
      · linarith [Real.pi_pos, h5]
      · nlinarith [Real.pi_pos, h6, Real.pi_gt_three]
    have h10 : Real.cos (Real.pi / 4 * x) ≥ 1 / 2 := by
      have h10 : Real.cos (Real.pi / 4 * x) ≥ Real.cos (Real.pi / 3) := by
        apply Real.cos_le_cos_of_nonneg_of_le_pi
        all_goals
          nlinarith [Real.pi_pos, h5, h6, Real.pi_gt_three]
      have h11 : Real.cos (Real.pi / 3) = 1 / 2 := by
        rw [Real.cos_pi_div_three]
      nlinarith
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num : (3 : ℝ) > 0), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (3 : ℝ) ≥ 0), Real.sin_sq_add_cos_sq (Real.pi / 4 * x)]