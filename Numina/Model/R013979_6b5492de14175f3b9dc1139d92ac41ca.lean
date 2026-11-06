import Mathlib

theorem algebra_188758 (x : ℝ) :
    3 * Real.sin (2 * x) ^ 2 + 7 * Real.cos (2 * x) - 3 = 0 ↔
    ∃ k : ℤ, x = (Real.pi / 4) * (2 * k + 1) := by
  constructor
  · -- First, prove the forward direction: if the equation holds, then x must be of the form π/4(2k+1).
    intro h
    have h1 : Real.sin (2 * x) ^ 2 = 1 - Real.cos (2 * x) ^ 2 := by
      have h2 : Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * x)
      linarith
    rw [h1] at h
    have h2 : Real.cos (2 * x) * (-3 * Real.cos (2 * x) + 7) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where Real.cos (2 * x) = 0
      have hcos0 : Real.cos (2 * x) = 0 := h3
      have h5 : ∃ k : ℤ, 2 * x = Real.pi / 2 + k * Real.pi := by
        rw [Real.cos_eq_zero_iff] at hcos0
        rcases hcos0 with ⟨k, hk⟩
        refine ⟨k, ?_⟩
        linarith
      rcases h5 with ⟨k, hk⟩
      use k
      have hk' : x = (Real.pi / 4) * (2 * k + 1) := by
        have eq1 : x = (Real.pi / 2 + k * Real.pi) / 2 := by
          linarith
        rw [eq1]
        have eq2 : (Real.pi / 2 + k * Real.pi) / 2 = (Real.pi / 4) * (2 * k + 1) := by
          field_simp at *
          <;> ring
        linarith [eq1, eq2]
      assumption
    · -- Case where -3 * Real.cos (2 * x) + 7 = 0
      have hcos73 : Real.cos (2 * x) = 7 / 3 := by
        linarith
      have h3 : -1 ≤ Real.cos (2 * x) ∧ Real.cos (2 * x) ≤ 1 := by
        constructor
        · apply Real.neg_one_le_cos
        · apply Real.cos_le_one
      nlinarith [hcos73, h3.1, h3.2]
  · -- Now the reverse direction.
    rintro ⟨k, hk⟩
    have h5 : 2 * x = Real.pi / 2 * (2 * k + 1) := by
      have h6 : x = (Real.pi / 4) * (2 * k + 1) := hk
      linarith [h6]
    have hk0 : Real.cos (2 * x) = 0 := by
      have hangle2 : 2 * x = Real.pi / 2 * (2 * k + 1) := h5
      have : Real.cos (2 * x) = Real.cos (Real.pi / 2 * (2 * k + 1)) := by
        rw [hangle2]
      rw [this]
      have eq1 : Real.cos (Real.pi / 2 * (2 * k + 1)) =
          Real.cos (Real.pi / 2 + (k : ℝ) * Real.pi) := by
        ring_nf
      rw [eq1]
      have eq2 : Real.cos (Real.pi / 2 + (k : ℝ) * Real.pi) = 0 := by
        have eq3 : Real.cos (Real.pi / 2 + (k : ℝ) * Real.pi) = Real.cos (Real.pi / 2) * Real.cos ((k : ℝ) * Real.pi) - Real.sin (Real.pi / 2) * Real.sin ((k : ℝ) * Real.pi) := by
          rw [Real.cos_add]
        rw [eq3]
        have cos_pi_div_2 : Real.cos (Real.pi / 2) = 0 := Real.cos_pi_div_two
        have sin_pi_div_2 : Real.sin (Real.pi / 2) = 1 := Real.sin_pi_div_two
        simp [cos_pi_div_2, sin_pi_div_2]
      assumption
    have hsin2x : Real.sin (2 * x) ^ 2 = 1 := by
      have h22 : Real.sin (2 * x) ^ 2 + Real.cos (2 * x) ^ 2 = 1 := Real.sin_sq_add_cos_sq (2 * x)
      rw [hk0] at h22
      nlinarith
    rw [hsin2x, hk0]
    all_goals nlinarith