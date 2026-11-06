import Mathlib

open Real Set
open scoped Real

theorem algebra_246225 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 2 + 2 * sin x * cos x + 3 * cos x ^ 2) :
  IsGreatest (range f) (2 + sqrt 2) ∧ IsLeast (range f) (2 - sqrt 2) := by 
  have h1 : ∀ x, f x = 2 + sin (2 * x) + cos (2 * x) := by
    intro x
    rw [h₀]
    have h3 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
    have h4 : sin (2 * x) = 2 * sin x * cos x := by
      rw [show 2 * x = 2 * x by rfl]
      rw [sin_two_mul]
      all_goals ring_nf 
      <;> linarith
    have h5 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by
      rw [show 2 * x = 2 * x by rfl]
      rw [cos_two_mul]
      all_goals linarith
    nlinarith [h3, h4, h5, Real.sin_sq_add_cos_sq x]
  constructor
  · -- Show that $2 + \sqrt{2}$ is greatest
    constructor 
    · -- Show that $2 + \sqrt{2}$ is in the range of $f$
      use (Real.pi / 8)
      have h2 : f (Real.pi / 8) = 2 + Real.sqrt 2 := by 
        rw [h1]
        have h6 : 2 * (Real.pi / 8) = Real.pi / 4 := by ring_nf
        rw [h6]
        have h7 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := Real.sin_pi_div_four
        have h8 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
        rw [h7, h8]
        linarith 
      linarith 
    · -- Show that $2 + \sqrt{2}$ is the greatest value in the range
      intro y 
      rintro ⟨x, hx⟩
      rw [h1 x] at hx
      have h6 : sin (2 * x) + cos (2 * x) ≤ Real.sqrt 2 := by
        have h7 : (sin (2 * x) + cos (2 * x)) ^ 2 ≤ 2 := by
          have h8 : sin (2 * x) ^ 2 + cos (2 * x) ^ 2 = 1 := by 
            have h9 : sin (2 * x) ^ 2 + cos (2 * x) ^ 2 = 1 := by 
              exact Real.sin_sq_add_cos_sq (2 * x)
            linarith
          nlinarith [Real.sin_sq_add_cos_sq (2 * x), sq_nonneg (sin (2 * x) - cos (2 * x)), sq_nonneg (sin (2 * x) + cos (2 * x)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin (2 * x) ^ 2 + cos (2 * x) ^ 2)]
        have h8 : sin (2 * x) + cos (2 * x) ≤ Real.sqrt 2 := by
          have h10 : (sin (2 * x) + cos (2 * x)) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            nlinarith [h7, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h11 : sin (2 * x) + cos (2 * x) ≤ Real.sqrt 2 := by nlinarith [show Real.sqrt 2 ≥ 0 by positivity, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          linarith 
        linarith
      nlinarith [Real.sqrt_nonneg 2, Real.sin_sq_add_cos_sq (2 * x), sq_nonneg (sin (2 * x) - cos (2 * x)), Real.sin_sq_add_cos_sq (2 * x), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that $2 - \sqrt{2}$ is least
    constructor 
    · -- Show that $2 - \sqrt{2}$ is in the range of $f$
      use (Real.pi / 8 + Real.pi / 2)
      have h7 : f (Real.pi / 8 + Real.pi / 2) = 2 - Real.sqrt 2 := by
        have h8 : f (Real.pi / 8 + Real.pi / 2) = 2 + sin (2 * (Real.pi / 8 + Real.pi / 2)) + cos (2 * (Real.pi / 8 + Real.pi / 2)) := by
          apply h1
        have h9 : 2 * (Real.pi / 8 + Real.pi / 2) = Real.pi / 4 + 2 * (Real.pi / 2) := by ring
        rw [h9] at h8
        have h10 : sin (Real.pi / 4 + 2 * (Real.pi / 2)) = - (Real.sqrt 2 / 2) := by 
          have h11 : sin (Real.pi / 4 + 2 * (Real.pi / 2)) = sin (Real.pi / 4 + Real.pi) := by ring_nf 
          rw [h11]
          have h12 : sin (Real.pi / 4 + Real.pi) = sin (Real.pi + Real.pi / 4) := by ring_nf 
          rw [h12]
          have h13 : sin (Real.pi + Real.pi / 4) = - sin (Real.pi / 4) := by
            rw [sin_add, sin_pi, cos_pi]
            all_goals 
              ring_nf 
              <;> norm_num 
            all_goals linarith
          rw [h13, Real.sin_pi_div_four]
          all_goals linarith
        have h14 : cos (Real.pi / 4 + 2 * (Real.pi / 2)) = - (Real.sqrt 2 / 2) := by
          have h15 : cos (Real.pi / 4 + 2 * (Real.pi / 2)) = cos (Real.pi / 4 + Real.pi) := by ring_nf 
          rw [h15]
          have h16 : cos (Real.pi / 4 + Real.pi) = cos (Real.pi + Real.pi / 4) := by ring_nf 
          rw [h16]
          have h17 : cos (Real.pi + Real.pi / 4) = - cos (Real.pi / 4) := by 
            rw [cos_add, sin_pi, cos_pi]
            all_goals 
              ring_nf 
              <;> norm_num 
              <;> nlinarith 
            all_goals linarith
          rw [h17, Real.cos_pi_div_four]
          all_goals linarith 
        rw [h10, h14] at h8
        nlinarith
      linarith
    · -- Show that $2 - \sqrt{2}$ is the least value in the range
      intro y 
      rintro ⟨x, hx⟩
      rw [h1 x] at hx
      have h6 : sin (2 * x) + cos (2 * x) ≥ -Real.sqrt 2 := by
        have h7 : (sin (2 * x) + cos (2 * x)) ^ 2 ≤ 2 := by
          have h8 : sin (2 * x) ^ 2 + cos (2 * x) ^ 2 = 1 := by 
            have h9 : sin (2 * x) ^ 2 + cos (2 * x) ^ 2 = 1 := by 
              exact Real.sin_sq_add_cos_sq (2 * x)
            linarith
          nlinarith [Real.sin_sq_add_cos_sq (2 * x), sq_nonneg (sin (2 * x) - cos (2 * x)), sq_nonneg (sin (2 * x) + cos (2 * x)), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (sin (2 * x) ^ 2 + cos (2 * x) ^ 2)]
        have h8 : sin (2 * x) + cos (2 * x) ≥ -Real.sqrt 2 := by
          have h10 : (sin (2 * x) + cos (2 * x)) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            nlinarith [h7, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          have h11 : sin (2 * x) + cos (2 * x) ≥ -Real.sqrt 2 := by
            nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
          linarith 
        linarith 
      nlinarith [Real.sqrt_nonneg 2, Real.sin_sq_add_cos_sq (2 * x), sq_nonneg (sin (2 * x) - cos (2 * x)), Real.sin_sq_add_cos_sq (2 * x), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]