import Mathlib

theorem algebra_224672 (θ : Real) (h : Real.sin θ + Real.cos θ = 6 / 5) :
    Real.tan θ + 1 / Real.tan θ = 50 / 11 := by
  have h1 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  have h2 : Real.sin θ * Real.cos θ = 11 / 50 := by
    have h3 : Real.sin θ + Real.cos θ = 6 / 5 := h
    have h4 : (Real.sin θ + Real.cos θ) ^ 2 = (6 / 5) ^ 2 := by
      rw [h3]
    have h5 : (Real.sin θ + Real.cos θ) ^ 2 = Real.sin θ ^ 2 + Real.cos θ ^ 2 + 2 * (Real.sin θ * Real.cos θ) := by
      ring
    rw [h5] at h4
    have h6 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
      linarith [Real.sin_sq_add_cos_sq θ]
    rw [h6] at h4
    linarith
  have h5 : Real.sin θ ≠ 0 := by
    by_contra h6
    have h7 : Real.sin θ = 0 := by linarith
    have h8 : Real.sin θ + Real.cos θ = 6 / 5 := h
    rw [h7] at h8
    have h9 : Real.cos θ ^ 2 = 1 := by
      have h50 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      rw [h7] at h50
      linarith
    have h10 : Real.cos θ ≤ 1 := by
      nlinarith [sq_nonneg (Real.cos θ), Real.sin_sq_add_cos_sq θ]
    have h11 : Real.cos θ = 6 / 5 := by nlinarith
    nlinarith [sq_nonneg (Real.cos θ - 1)]
  have h6 : Real.cos θ ≠ 0 := by
    by_contra h7
    have h8 : Real.cos θ = 0 := by linarith
    have h9 : Real.sin θ + Real.cos θ = 6 / 5 := h
    rw [h8] at h9
    have h10 : Real.sin θ ^ 2 = 1 := by
      have h54 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
      rw [h8] at h54
      linarith
    have h11 : Real.sin θ ≤ 1 := by
      nlinarith [sq_nonneg (Real.sin θ), Real.sin_sq_add_cos_sq θ]
    have h12 : Real.sin θ = 1 ∨ Real.sin θ = -1 := by
      have h16 : Real.sin θ ^ 2 = 1 := h10
      have : Real.sin θ = 1 ∨ Real.sin θ = -1 := by
        rw [sq_eq_one_iff] at h16
        tauto
      assumption
    rcases h12 with h13 | h14
    · -- If sin θ = 1
      nlinarith
    · -- If sin θ = -1
      nlinarith
  have htan : Real.tan θ = Real.sin θ / Real.cos θ := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [htan]
  have h8 : Real.sin θ / Real.cos θ + 1 / (Real.sin θ / Real.cos θ) = (Real.sin θ ^ 2 + Real.cos θ ^ 2) / (Real.sin θ * Real.cos θ) := by
    have h81 : Real.sin θ ≠ 0 := h5
    have h82 : Real.cos θ ≠ 0 := h6
    have htan_eq : 1 / (Real.sin θ / Real.cos θ) = Real.cos θ / Real.sin θ := by 
      field_simp [h81, h82]
    rw [htan_eq]
    have h9 : Real.sin θ / Real.cos θ + Real.cos θ / Real.sin θ = (Real.sin θ ^ 2 + Real.cos θ ^ 2) / (Real.sin θ * Real.cos θ) := by
      field_simp [h81, h82]
      <;> ring_nf 
      <;> nlinarith [Real.sin_sq_add_cos_sq θ]
    linarith
  rw [h8]
  have h7 : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [h7]
  rw [h2]
  all_goals norm_num
  <;> nlinarith