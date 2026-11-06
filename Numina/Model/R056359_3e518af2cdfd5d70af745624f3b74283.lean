import Mathlib

theorem algebra_320418 (a b c : ℝ) (h₀ : a + b + c = 0) (h₁ : a * b * c = 8) :
    c < 0 ∨ c ≥ 2 * (4 ^ ((1 : ℝ) / 3)) := by
  by_cases h2 : c < 0
  · left
    linarith
  push_neg at h2
  have h3 : c ≥ 0 := by linarith
  have h4 : c > 0 := by
    by_contra h
    push_neg at h
    have h5 : c = 0 := by linarith [h3, h]
    rw [h5] at h₁
    nlinarith
  have h5 : a + b = -c := by linarith [h₀]
  have h6 : a * b = 8 / c := by
    have h7 : c ≠ 0 := by nlinarith
    field_simp
    nlinarith [h₁, h7]
  have h8 : (a - b) ^ 2 ≥ 0 := by nlinarith
  have h10 : c ^ 2 - 32 / c ≥ 0 := by
    have h4 : c > 0 := h4
    have h12 : a * b = 8 / c := h6
    have h13 : (a - b) ^ 2 ≥ 0 := h8
    have h14 : (a + b) ^ 2 ≥ 4 * (a * b) := by
      nlinarith [sq_nonneg (a - b)]
    have h15 : (a + b) ^ 2 = c ^ 2 := by
      rw [h5]
      ring
    have h16 : 4 * (a * b) = 4 * (8 / c) := by
      linarith [h12]
    have h17 : c > 0 := h4
    have h18 : (a + b) ^ 2 - 4 * (a * b) = c ^ 2 - 32 / c := by
      rw [h15, h16]
      field_simp [show c ≠ 0 by nlinarith]
      <;> nlinarith
    nlinarith [h14, h18]
  have h17 : c ^ 3 ≥ 32 := by
    have h4 : c > 0 := h4
    have h10 : c ^ 2 - 32 / c ≥ 0 := h10
    have h12 : c ^ 3 - 32 ≥ 0 := by
      have h18 : c > 0 := h4
      have h19 : c ^ 2 - 32 / c ≥ 0 := h10
      have h23 : (c ^ 2 - 32 / c) = (c ^ 3 - 32) / c := by
        field_simp [show c ≠ 0 by linarith]
        <;> ring
      have h24 : (c ^ 3 - 32) / c ≥ 0 := by linarith [h23, h19]
      have h25 : c ^ 3 - 32 ≥ 0 := by
        apply (div_nonneg_iff).mp at h24
        cases h24 with
        | inl h26 =>
          linarith [h26]
        | inr h27 =>
          linarith [show c > 0 from h4]
      linarith [h25]
    nlinarith [h12]
  have h18 : c ≥ 2 * (4 ^ ((1 : ℝ) / 3)) := by
    have h19 : c ^ 3 ≥ 32 := h17
    have h20 : (4 : ℝ) ^ ((1 : ℝ) / 3) ≥ 0 := by positivity
    have h21 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 32 := by
      ring_nf
      have h22 : ((4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = (4 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul]
        norm_num
        all_goals linarith [show (0 : ℝ) ≤ (4 : ℝ) by norm_num]
      rw [h22]
      norm_num
    have h23 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ c ^ 3 := by linarith [h21, h19]
    have h24 : 2 * (4 : ℝ) ^ ((1 : ℝ) / 3) ≤ c := by
      have h25 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ c ^ 3 := h23
      have h26 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - c ^ 3 ≤ 0 := by linarith
      have h27 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 - c ^ 3 = (2 * (4 : ℝ) ^ ((1 : ℝ) / 3) - c) * ((2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) * c + c ^ 2) := by ring
      rw [h27] at h26
      have h28 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) ^ 2 + (2 * (4 : ℝ) ^ ((1 : ℝ) / 3)) * c + c ^ 2 > 0 := by
        nlinarith [sq_nonneg (2 * (4 : ℝ) ^ ((1 : ℝ) / 3) - c), sq_nonneg (2 * (4 : ℝ) ^ ((1 : ℝ) / 3) + c), show (0 : ℝ) < (4 : ℝ) ^ ((1 : ℝ) / 3) by positivity]
      have h29 : (2 * (4 : ℝ) ^ ((1 : ℝ) / 3) - c) ≤ 0 := by nlinarith [h26, h28]
      linarith
    linarith [h24]
  right
  linarith [h18]