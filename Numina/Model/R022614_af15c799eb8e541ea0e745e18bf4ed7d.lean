import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_146785 {f : ℝ → ℝ}
  (hf : f = λ x => (cos x)^3 / sin x + (sin x)^3 / cos x) :
  IsLeast (image f (Ioo 0 (π/2))) 1 := by

  constructor
  · -- Show that 1 is in the image.
    use Real.pi / 4
    constructor
    · -- Show that π/4 is in (0, π/2).
      exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    · -- Show that f (π / 4) = 1.
      rw [hf]
      have h1 : cos (Real.pi / 4) = Real.sqrt 2 / 2 := by
        rw [cos_pi_div_four]
      have h2 : sin (Real.pi / 4) = Real.sqrt 2 / 2 := by 
        rw [sin_pi_div_four]
      simp only [h1, h2]
      have h3 : Real.sqrt 2 > 0 := by positivity
      have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num)
      have eq1 : (Real.sqrt 2 / 2 : ℝ) ^ 3 / (Real.sqrt 2 / 2) = (Real.sqrt 2 / 2) ^ 2 := by 
        field_simp 
        <;> nlinarith
      have eq3 : (Real.sqrt 2 / 2 : ℝ) ^ 2 + (Real.sqrt 2 / 2 : ℝ) ^ 2 = 1 := by
        nlinarith [h4, Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num)]
      linarith [eq1, eq3]

  · -- Show that 1 is the least.
    intro y hy
    rcases hy with ⟨x, hx, hfx⟩
    rw [hf] at hfx 
    have h1 : 0 < x := by
      have hx0 : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := by 
        simpa using hx 
      rcases hx0 with ⟨hx0, hx1⟩ 
      linarith 
    have h2 : x < Real.pi / 2 := by 
      have hx0 : x ∈ Ioo (0 : ℝ) (Real.pi / 2) := by 
        simpa using hx 
      rcases hx0 with ⟨hx0, hx1⟩ 
      linarith
    have h3 : 0 < sin x := by 
      apply sin_pos_of_pos_of_lt_pi 
      all_goals linarith [Real.pi_pos, Real.pi_gt_three]
    have h4 : 0 < cos x := by 
      apply cos_pos_of_mem_Ioo 
      constructor <;> linarith [Real.pi_pos, Real.pi_gt_three, h1, h2]
    have h5 : (cos x) ^ 3 / sin x + (sin x) ^ 3 / cos x ≥ 1 := by 
      have h5' : sin x * cos x > 0 := mul_pos h3 h4 
      have h6 : (cos x) ^ 3 / sin x + (sin x) ^ 3 / cos x - 1 ≥ 0 := by
        have h7 : (cos x) ^ 3 / sin x + (sin x) ^ 3 / cos x - 1 = 
            ( (cos x) ^ 4 + (sin x) ^ 4 - (sin x * cos x) ) / (sin x * cos x) := by 
          field_simp [h3, h4]
          <;> ring 
        rw [h7]
        apply div_nonneg 
        · -- Show that numerator is non-negative. 
          nlinarith [sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x * cos x - 1 / 2), sq_nonneg (sin x ^ 2 + cos x ^ 2 - 1), sq_nonneg (sin x + cos x), sq_nonneg (sin x - cos x), Real.sin_sq_add_cos_sq x, h3, h4, sq_nonneg (sin x ^ 2 - cos x ^ 2 : ℝ), sq_nonneg (sin x * cos x : ℝ)]
        · -- Show denominator is positive.
          positivity 
      linarith 
    have eq1 : (cos x) ^ 3 / sin x + (sin x) ^ 3 / cos x = y := by 
      simpa using hfx 
    have eq2 : y = (cos x) ^ 3 / sin x + (sin x) ^ 3 / cos x := by 
      linarith [eq1]
    linarith [eq2, h5]