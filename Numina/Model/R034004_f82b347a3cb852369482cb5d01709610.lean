import Mathlib

open Real Set
open scoped Real

/- The maximum value of the function $f(x)={{\sin }^{4}}x+\sin x\cos x+{{\cos }^{4}}x$ is ___          ___. -/
theorem algebra_12411 (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = sin x ^ 4 + sin x * cos x + cos x ^ 4) :
  IsGreatest (range f) (9/8) := by
  constructor
  · -- First, we show 9/8 is in the range
    use Real.pi / 12
    have h1 : f (Real.pi / 12) = 9 / 8 := by
      rw [h₀]
      have h2 : sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2 = 1 := by
        exact Real.sin_sq_add_cos_sq (Real.pi / 12)
      have h3 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 = 7 / 8 := by
        have h4 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 = (sin (Real.pi / 12) ^ 2 + cos (Real.pi / 12) ^ 2) ^ 2 - 2 * (sin (Real.pi / 12) * cos (Real.pi / 12)) ^ 2 := by
          ring
        rw [h4, h2]
        have h5 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
          have h6 : sin (2 * (Real.pi / 12)) = 2 * sin (Real.pi / 12) * cos (Real.pi / 12) := by
            rw [sin_two_mul]
          have h7 : sin (2 * (Real.pi / 12)) = 1 / 2 := by
            have h8 : 2 * (Real.pi / 12) = Real.pi / 6 := by ring
            rw [h8]
            have h9 : sin (Real.pi / 6) = 1 / 2 := by
              exact sin_pi_div_six
            linarith [h9]
          have h11 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
            nlinarith [h6, h7]
          linarith [h11]
        rw [h5]
        norm_num
      have h5 : sin (Real.pi / 12) ^ 4 + sin (Real.pi / 12) * cos (Real.pi / 12) + cos (Real.pi / 12) ^ 4 = 9 / 8 := by
        have h6 : sin (Real.pi / 12) ^ 4 + cos (Real.pi / 12) ^ 4 = 7 / 8 := h3
        have h5 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
          have h6 : sin (2 * (Real.pi / 12)) = 2 * sin (Real.pi / 12) * cos (Real.pi / 12) := by
            rw [sin_two_mul]
          have h7 : sin (2 * (Real.pi / 12)) = 1 / 2 := by
            have h8 : 2 * (Real.pi / 12) = Real.pi / 6 := by ring
            rw [h8]
            have h9 : sin (Real.pi / 6) = 1 / 2 := by
              exact sin_pi_div_six
            linarith [h9]
          have h11 : sin (Real.pi / 12) * cos (Real.pi / 12) = 1 / 4 := by
            nlinarith [h6, h7]
          linarith [h11]
        nlinarith [h6, h5]
      linarith [h5]
    linarith [h1]
  · -- Show no value greater than 9/8 is in the range
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [h₀] at hx
    have h5 : sin x ^ 4 + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 := by
      have h51 : sin x ^ 2 + cos x ^ 2 = 1 := by 
        exact Real.sin_sq_add_cos_sq x
      have h52 : sin x ^ 4 + cos x ^ 4 = (sin x ^ 2 + cos x ^ 2) ^ 2 - 2 * (sin x * cos x) ^ 2 := by
        ring
      rw [h51] at h52 
      linarith
    have h6 : sin x ^ 4 + sin x * cos x + cos x ^ 4 = 1 - 2 * (sin x * cos x) ^ 2 + (sin x * cos x) := by 
      linarith [h5]
    have h7 : (sin x * cos x) ^ 2 ≤ 1 / 4 := by
      have h9 : sin x * cos x = (1 / 2) * (sin (2 * x)) := by
        have h13 : sin (2 * x) = 2 * sin x * cos x := by 
          rw [show 2 * x = 2 * x by rfl]
          rw [sin_two_mul]
        linarith [h13]
      have h14 : (sin x * cos x) ^ 2 = (1 / 4) * (sin (2 * x) ) ^ 2 := by 
        rw [h9]
        ring
      have h15 : (sin (2 * x) ) ^ 2 ≤ 1 := by 
        have h16 : (sin (2 * x)) ^ 2 ≤ 1 := by 
          apply sin_sq_le_one
        linarith [h16]
      nlinarith [h14, h15]
    have h8 : sin x ^ 4 + sin x * cos x + cos x ^ 4 ≤ 9 / 8 := by
      nlinarith [sq_nonneg (sin x * cos x - 1 / 4), sq_nonneg (sin x * cos x + 1 / 4), Real.sin_sq_add_cos_sq x, h7]
    linarith [h6, h8]