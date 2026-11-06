import Mathlib

theorem algebra_228319 {A ω φ : ℝ} (hA : A ≠ 0) (hω : ω ≠ 0) :
    (∀ x, A * Real.cos (ω * x + φ) = -A * Real.cos (ω * (-x) + φ)) ↔
    ∃ k : ℤ, φ = k * Real.pi + Real.pi / 2 := by
  constructor
  · -- Assume the graph is symmetric, prove ∃ k : ℤ, φ = k * Real.pi + Real.pi / 2
    intro h
    have h1 : ∀ x, A * Real.cos (ω * x + φ) = -A * Real.cos (ω * (-x) + φ) := h
    have h2 := h1 0
    have h3 : A * Real.cos φ = -A * Real.cos φ := by
      have h3 : A * Real.cos (ω * (0 : ℝ) + φ) = -A * Real.cos (ω * (- (0 : ℝ)) + φ) := by
        simpa using h2
      have h4 : A * Real.cos (ω * (0 : ℝ) + φ) = A * Real.cos φ := by
        simp [show ω * (0 : ℝ) = (0 : ℝ) by ring]
      have h5 : -A * Real.cos (ω * (- (0 : ℝ)) + φ) = -A * Real.cos φ := by
        have h6 : ω * (- (0 : ℝ)) = (0 : ℝ) := by ring
        rw [h6]
        all_goals simp
      rw [h4, h5] at h3
      linarith
    have h4 : Real.cos φ = 0 := by
      apply (mul_left_inj' hA).mp
      linarith
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.1 h4
    use k
    all_goals
      linarith
  · -- Assume ∃ k : ℤ, φ = k * Real.pi + Real.pi / 2, prove the symmetry condition
    rintro ⟨k, hk⟩
    intro x
    have h10 : Real.cos (ω * x + φ) = - Real.cos (ω * (-x) + φ) := by
      have h11 : Real.cos (ω * x + φ) + Real.cos (ω * (-x) + φ) = 0 := by
        have h12 : Real.cos (ω * x + φ) + Real.cos (ω * (-x) + φ) = 2 * Real.cos (ω * x) * Real.cos φ := by
          have h13 : Real.cos (ω * x + φ) = Real.cos (ω * x) * Real.cos φ - Real.sin (ω * x) * Real.sin φ := by
            rw [Real.cos_add]
          have h14 : Real.cos (ω * (-x) + φ) = Real.cos (ω * (-x)) * Real.cos φ - Real.sin (ω * (-x)) * Real.sin φ := by
            rw [Real.cos_add]
          have h15 : Real.cos (ω * (-x)) = Real.cos (ω * x) := by
            have : ω * (-x) = - (ω * x) := by ring
            rw [this]
            rw [Real.cos_neg]
          have h16 : Real.sin (ω * (-x)) = - Real.sin (ω * x) := by
            have : ω * (-x) = - (ω * x) := by ring
            rw [this]
            rw [Real.sin_neg]
          rw [h13, h14, h15, h16]
          all_goals ring
        have h13 : Real.cos φ = 0 := by
          rw [hk] 
          have h9 : Real.cos (↑k * Real.pi + Real.pi / 2 : ℝ) = 0 := by
            have h7 : Real.cos (↑k * Real.pi + Real.pi / 2 : ℝ) =
                Real.cos (↑k * Real.pi) * Real.cos (Real.pi / 2) - Real.sin (↑k * Real.pi) * Real.sin (Real.pi / 2) := by
              rw [Real.cos_add]
            have h10 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
            have h11 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
            have h12 : Real.sin (↑k * Real.pi) = 0 := by
              have h14 : Real.sin (↑k * Real.pi) = 0 := by
                simp [Real.sin_int_mul_pi]
              exact h14
            rw [h10, h11, h12] at h7
            nlinarith [Real.cos_sq_add_sin_sq (↑k * Real.pi)]
          linarith
        rw [h12, h13]
        all_goals ring
      linarith
    have h1 : A * Real.cos (ω * x + φ) = -A * Real.cos (ω * (-x) + φ) := by
      have h10' : Real.cos (ω * x + φ) = - Real.cos (ω * (-x) + φ) := h10
      have : A * Real.cos (ω * x + φ) = -A * Real.cos (ω * (-x) + φ) := by
        have h12 : Real.cos (ω * x + φ) = - Real.cos (ω * (-x) + φ) := h10
        have : A * Real.cos (ω * x + φ) = A * (- Real.cos (ω * (-x) + φ)) := by
          rw [h12]
        rw [this]
        all_goals ring
      linarith
    simpa using h1