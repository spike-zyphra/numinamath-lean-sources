import Mathlib

open Real Set

theorem algebra_5655 {x : ℝ} (hx : x ∈ Icc 0 1) :
    arcsin x + arcsin (1 - x) = arccos x ↔ x = 0 ∨ x = 1 / 2 := by
  rcases hx with ⟨hx0, hx1⟩
  constructor
  · -- Assume arcsin x + arcsin (1 - x) = arccos x, prove x = 0 ∨ x = 1 / 2
    intro h
    have h1 : arcsin x + arcsin (1 - x) = arccos x := h
    have h2 : x ≥ 0 := by linarith
    have h3 : x ≤ 1 := by linarith
    have h4 : (1 - x) ≥ 0 := by linarith
    have h5 : (1 - x) ≤ 1 := by linarith
    have h7 : sin (arcsin x + arcsin (1 - x)) = sin (arccos x) := by
      rw [show arcsin x + arcsin (1 - x) = arccos x by linarith [h1]]
    have h8 : sin (arcsin x + arcsin (1 - x)) = sin (arcsin x) * cos (arcsin (1 - x)) + cos (arcsin x) * sin (arcsin (1 - x)) := by
      rw [sin_add]
    have h9 : sin (arccos x) = Real.sqrt (1 - x^2) := by 
      rw [sin_arccos]
    rw [h8, h9] at h7
    have h10 : sin (arcsin x) = x := by 
      apply sin_arcsin
      linarith
      linarith
    have h11 : sin (arcsin (1 - x)) = 1 - x := by 
      apply sin_arcsin
      linarith
      linarith
    have h12 : cos (arcsin (1 - x)) = Real.sqrt (1 - (1 - x)^2) := by 
      rw [cos_arcsin]
    have h13 : cos (arcsin x) = Real.sqrt (1 - x^2) := by
      rw [cos_arcsin]
    rw [h10, h11, h12, h13] at h7
    by_cases h16 : x = 0 
    · left 
      exact h16 
    · -- x ≠ 0, so we can derive Real.sqrt (2 * x - x ^ 2) - Real.sqrt (1 - x^2) = 0 
      have h17 : x ≠ 0 := by 
        intro h 
        apply h16 
        linarith 
      -- Rearranging h7: x * Real.sqrt (1 - (1 - x)^2) + Real.sqrt (1 - x^2) * (1 - x) = Real.sqrt (1 - x^2) 
      -- Rearranging further: x * Real.sqrt (1 - (1 - x)^2) + Real.sqrt (1 - x^2) * ( (1 - x) - 1 ) = 0 
      -- Simplify to: x * Real.sqrt (1 - (1 - x)^2) - Real.sqrt (1 - x^2) * x = 0
      -- Rearranged to: x * ( Real.sqrt (1 - (1 - x)^2) - Real.sqrt (1 - x^2) ) = 0 
      have h14 : Real.sqrt (1 - (1 - x)^2) = Real.sqrt (2 * x - x^2) := by 
        have h14 : (1 - (1 - x) ^ 2 : ℝ) = 2 * x - x^2 := by 
          ring 
        rw [h14] 
      rw [h14] at h7
      have h18 : x * (Real.sqrt (2 * x - x ^ 2) - Real.sqrt (1 - x ^ 2)) = 0 := by 
        nlinarith 
      have h19 : Real.sqrt (2 * x - x ^ 2) = Real.sqrt (1 - x ^ 2) := by 
        apply (mul_right_inj' (show x ≠ 0 by exact h17)).mp 
        -- Divide both sides by x which is non-zero
        linarith 
      have h20 : 2 * x - x^2 = 1 - x^2 := by 
        calc
          2 * x - x^2 = (Real.sqrt (2 * x - x^2)) ^ 2 := by 
            rw [Real.sq_sqrt] 
            nlinarith
          _ = (Real.sqrt (1 - x^2)) ^ 2 := by 
            rw [h19]
          _ = 1 - x^2 := by 
            rw [Real.sq_sqrt] 
            nlinarith 
      have h21 : x = 1 / 2 := by 
        nlinarith 
      right 
      linarith 
  · -- Assume x = 0 or x = 1/2, prove arcsin x + arcsin (1 - x) = arccos x
    rintro (h | h)
    · -- x = 0 
      rw [h] 
      norm_num [arcsin_zero, arcsin_one, arccos_zero] 
    · -- x = 1/2 
      rw [h] 
      have h1 : arcsin (1 / 2 : ℝ) = Real.pi / 6 := by 
        have h1 : sin (Real.pi / 6 : ℝ) = 1 / 2 := by 
          exact sin_pi_div_six 
        rw [← h1] 
        apply arcsin_sin 
        all_goals linarith [Real.pi_pos] 
      have h1' : arcsin (1 - (1 / 2 : ℝ) ) = Real.pi / 6 := by 
        have h12 : (1 - (1 / 2 : ℝ) ) = (1 / 2 : ℝ) := by 
          norm_num 
        rw [h12] 
        linarith [h1] 
      have h2 : arcsin (1 / 2 : ℝ) = Real.pi / 6 := h1 
      have h3 : arcsin (1 / 2 : ℝ) + arcsin (1 - (1 / 2 : ℝ) ) = 2 * (Real.pi / 6) := by 
        linarith [h1, h1']
      have h4 : arcsin (1 / 2 : ℝ) + arcsin (1 - (1 / 2 : ℝ) ) = Real.pi / 3 := by 
        linarith [h3, Real.pi_pos] 
      have h5 : arccos (1 / 2 : ℝ) = Real.pi / 3 := by 
        have h6 : cos (Real.pi / 3 : ℝ) = 1 / 2 := by 
          exact cos_pi_div_three 
        rw [← h6] 
        apply arccos_cos 
        all_goals linarith [Real.pi_pos] 
      linarith [h4, h5]