import Mathlib

open Complex

theorem algebra_22197 {z1 z2 : ℂ} (h : ∃ r : ℝ, z2 / z1 = I * r) (h' : 2 * z1 ≠ 7 * z2) :
    ‖(2 * z1 + 7 * z2) / (2 * z1 - 7 * z2)‖ = 1 := by
  rcases h with ⟨r, hr⟩
  by_cases h1 : z1 = 0
  · 
    have h2 : z1 = 0 := h1
    have hr0 : z2 / z1 = 0 := by
      rw [h2]
      norm_num
    have hr_eq : I * r = 0 := by
      rw [show z2 / z1 = 0 by exact hr0] at hr
      simpa using hr
    have hr0 : r = 0 := by
      simpa using congr_arg Complex.im hr_eq
    have h3 : 2 * z1 + 7 * z2 = 7 * z2 := by
      rw [show z1 = 0 by exact h1]
      ring
    have h4 : 2 * z1 - 7 * z2 = -7 * z2 := by
      rw [show z1 = 0 by exact h1]
      ring
    have h5 : z2 ≠ 0 := by
      intro h5
      have : 2 * z1 = 7 * z2 := by
        rw [show z1 = 0 by exact h1, h5]
        norm_num
      tauto
    have h6 : (2 * z1 + 7 * z2) / (2 * z1 - 7 * z2) = -1 := by
      rw [h3, h4]
      have h7 : z2 ≠ 0 := h5
      field_simp [h7]
    rw [h6]
    simp
  · 
    have h1' : z1 ≠ 0 := h1
    have h2 : z2 = I * r * z1 := by
      have h3 : z2 / z1 = I * r := hr
      have h4 : z2 = (z2 / z1) * z1 := by
        field_simp [h1']
      rw [h3] at h4
      simpa using h4
    have h4 : ‖(2 * z1 + 7 * z2) / (2 * z1 - 7 * z2)‖ = Complex.abs ((2 * z1 + 7 * z2) / (2 * z1 - 7 * z2) : ℂ) := by
      simp [Complex.norm_eq_abs]
    rw [h4]
    have h5 : Complex.abs ((2 * z1 + 7 * z2) / (2 * z1 - 7 * z2)) = Complex.abs (2 * z1 + 7 * z2) / Complex.abs (2 * z1 - 7 * z2) := by
      field_simp [Complex.abs, h1']
    rw [h5]
    have h6 : Complex.abs (2 * z1 + 7 * z2) = Complex.abs (2 * z1 - 7 * z2) := by
      have h7 : z2 = I * r * z1 := h2
      have h8 : 2 * z1 + 7 * z2 = (2 + 7 * I * r) * z1 := by
        rw [h7]
        ring_nf
      have h9 : 2 * z1 - 7 * z2 = (2 - 7 * I * r) * z1 := by
        rw [h7]
        ring_nf
      rw [h8, h9]
      have h11 : Complex.abs ((2 + 7 * I * r) * z1) = Complex.abs (2 + 7 * I * r) * Complex.abs z1 := by
        simp [Complex.abs, Complex.normSq]
      have h12 : Complex.abs ((2 - 7 * I * r) * z1) = Complex.abs (2 - 7 * I * r) * Complex.abs z1 := by
        simp [Complex.abs, Complex.normSq]
      rw [h11, h12]
      have h13 : Complex.abs (2 + 7 * I * r) = Complex.abs (2 - 7 * I * r) := by
        simp [Complex.abs, Complex.normSq]
        all_goals
          ring_nf
      have h14 : Complex.abs z1 > 0 := by
        have h14 : z1 ≠ 0 := h1'
        have h15 : Complex.abs z1 > 0 := by
          by_contra h
          push_neg at h
          have h17 : Complex.abs z1 = 0 := by
            linarith [show Complex.abs z1 ≥ 0 by positivity]
          have h19 : z1 = 0 := by
            simp at h17 ⊢
            try tauto
          contradiction
        exact h15
      have h15 : Complex.abs (2 + 7 * I * r) = Complex.abs (2 - 7 * I * r) := h13
      nlinarith
    have h8 : Complex.abs (2 * z1 - 7 * z2) > 0 := by
      have h17 : 2 * z1 - 7 * z2 ≠ 0 := by
        intro h
        have : 2 * z1 = 7 * z2 := by
          have h3 : 2 * z1 - 7 * z2 = 0 := by
            exact h
          calc
            2 * z1 = (2 * z1 - 7 * z2) + 7 * z2 := by ring
            _ = 0 + 7 * z2 := by rw [h3]
            _ = 7 * z2 := by ring
        tauto
      have h18 : Complex.abs (2 * z1 - 7 * z2) > 0 := by
        by_contra h
        push_neg at h
        have h20 : Complex.abs (2 * z1 - 7 * z2) = 0 := by
          linarith [show Complex.abs (2 * z1 - 7 * z2) ≥ 0 by positivity]
        have h21 : 2 * z1 - 7 * z2 = 0 := by
          simp at h20 ⊢
          try tauto
        contradiction
      exact h18
    have h11 : Complex.abs (2 * z1 + 7 * z2) / Complex.abs (2 * z1 - 7 * z2) = 1 := by
      have h12 : Complex.abs (2 * z1 + 7 * z2) = Complex.abs (2 * z1 - 7 * z2) := h6
      have h13 : Complex.abs (2 * z1 - 7 * z2) > 0 := h8
      field_simp [h13]
      all_goals linarith [h12]
    exact h11