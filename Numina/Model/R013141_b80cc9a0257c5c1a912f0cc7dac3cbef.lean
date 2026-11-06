import Mathlib

theorem algebra_227505 (f : ℝ → ℝ) (h : ∀ x, Real.cos (17 * x) = f (Real.cos x)) :
    ∀ x, Real.sin (17 * x) = f (Real.sin x) := by
  intro x
  have h1 := h (x - Real.pi / 2)
  have h2 : Real.cos (17 * (x - Real.pi / 2)) = Real.sin (17 * x) := by
    have h2a : Real.cos (17 * (x - Real.pi / 2)) = Real.sin (17 * x) := by
      have h3 : 17 * (x - Real.pi / 2) = 17 * x - 8.5 * Real.pi := by
        ring_nf
      rw [h3]
      have h5 : Real.cos (17 * x - 8.5 * Real.pi) = Real.cos (17 * x - Real.pi / 2) := by
        have h6 : 17 * x - 8.5 * Real.pi = (17 * x - Real.pi / 2) - 4 * (2 * Real.pi) := by
          ring_nf
        rw [h6]
        have h7 : Real.cos ((17 * x - Real.pi / 2) - 4 * (2 * Real.pi)) = Real.cos (17 * x - Real.pi / 2) := by
          have h8 : Real.cos ((17 * x - Real.pi / 2) - 4 * (2 * Real.pi)) = Real.cos ((17 * x - Real.pi / 2) - (4 : ℕ) * (2 * Real.pi)) := by
            norm_num
          rw [h8]
          rw [Real.cos_sub_nat_mul_two_pi]
        linarith
      have h8 : Real.cos (17 * x - Real.pi / 2) = Real.sin (17 * x) := by
        have h9 : Real.cos (17 * x - Real.pi / 2) = Real.cos (17 * x) * Real.cos (Real.pi / 2) + Real.sin (17 * x) * Real.sin (Real.pi / 2) := by
          rw [Real.cos_sub]
        have h10 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
        have h11 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
        rw [h10, h11] at h9
        linarith
      linarith
    linarith
  have h3 : Real.cos (x - Real.pi / 2) = Real.sin x := by
    have h4 : Real.cos (x - Real.pi / 2) = Real.cos x * Real.cos (Real.pi / 2) + Real.sin x * Real.sin (Real.pi / 2) := by
      rw [Real.cos_sub]
    have h6 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
    have h7 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
    rw [h6, h7] at h4
    linarith
  -- h1: f (cos (x - π / 2)) = cos (17 * (x - π / 2))
  -- h2: cos (17 * (x - π / 2)) = sin (17 * x)
  -- h3: cos (x - π / 2) = sin x
  -- goal: sin (17 * x) = f (sin x)
  rw [h3] at h1
  rw [h2] at h1
  linarith