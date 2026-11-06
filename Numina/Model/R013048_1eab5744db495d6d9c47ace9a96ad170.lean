import Mathlib

theorem algebra_245121 {x1 x2 k : ℝ} (hx1 : x1^2 + k * x1 + 1 = 0) (hx2 : x2^2 + k * x2 + 1 = 0)
    (hxy : x1 ≠ x2) :
    (x1 / x2)^2 + (x2 / x1)^2 > 2 ↔ k < -2 ∨ k > 2 := by

  have h3 : x1^2 + k * x1 + 1 - (x2 ^ 2 + k * x2 + 1) = 0 := by linarith
  have h4 : (x1 - x2) * (x1 + x2 + k) = 0 := by
    nlinarith
  have h5 : x1 + x2 + k = 0 := by
    apply_fun (fun y => y / (x1 - x2)) at h4
    field_simp [sub_ne_zero.mpr hxy] at h4 ⊢
    <;> nlinarith
  have h6 : x1 * x2 = 1 := by
    nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr hxy), sq_nonneg (x1 - x2), sq_nonneg (x1 + x2 + k), h3, sq_nonneg (x1 + x2), sq_nonneg (x1 - x2)]

  have hx1_ne_zero : x1 ≠ 0 := by
    by_contra h
    rw [h] at h6
    nlinarith
  have hx2_ne_zero : x2 ≠ 0 := by
    by_contra h
    rw [h] at h6
    nlinarith

  constructor
  · -- Assume (x1 / x2)^2 + (x2 / x1)^2 > 2, prove k < -2 ∨ k > 2
    intro h
    have h7 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 > 2 := h

    have h8 : x1^4 + x2^4 > 2 := by
      have h9 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 = (x1^4 + x2^4) / (x1^2 * x2^2) := by
        field_simp [hx2_ne_zero, hx1_ne_zero]
        <;> ring
      have h10 : x1^2 * x2^2 = 1 := by
        nlinarith [h6, sq_nonneg (x1 * x2), sq_nonneg (x1 * x2 - 1)]
      have h11 : (x1^4 + x2^4) / (x1^2 * x2^2) > 2 := by
        linarith [h9, h7]
      have h13 : x1^2 * x2^2 > 0 := by
        nlinarith [h10]
      have h12 : x1^4 + x2^4 > 2 := by
        have h14 : (x1^4 + x2^4) / (x1^2 * x2^2) > 2 := h11
        apply (lt_div_iff₀ (by positivity)).mp at h14
        nlinarith [h10]
      linarith
    have h9 : x1^4 + x2^4 = ((x1^2 + x2^2) ^ 2) - 2 * (x1 * x2) ^ 2 := by
      ring
    have h10 : x1 ^ 2 + x2 ^ 2 = k ^ 2 - 2 := by
      nlinarith [h5, h6, sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (k), sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)]
    rw [h10, h6] at h9
    have h11 : k ^ 2 > 4 := by
      nlinarith [h9, h8]

    by_contra h
    push_neg at h
    nlinarith [sq_nonneg (k ^ 2 - 4), sq_nonneg (k), sq_nonneg (k ^ 2 - 4)]
  · -- Assume k < -2 ∨ k > 2, prove (x1 / x2)^2 + (x2 / x1)^2 > 2
    intro h
    rcases h with (h | h)
    · -- k < -2 
      have h1 : k ^ 2 > 4 := by nlinarith
      have h8 : x1 ^ 4 + x2 ^ 4 > 2 := by
        have h9 : x1 ^ 4 + x2 ^ 4 = ((x1^2 + x2^2) ^ 2) - 2 * (x1 * x2) ^ 2 := by
          ring
        have h10 : x1 ^ 2 + x2 ^ 2 = k ^ 2 - 2 := by
          nlinarith [h5, h6, sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (k), sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)]
        rw [h10, h6] at h9
        nlinarith [h9, h1]
      have h7 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 > 2 := by
        have h9 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 = (x1^4 + x2^4) / (x1^2 * x2^2) := by
          field_simp [hx2_ne_zero, hx1_ne_zero]
          <;> ring
        have h10 : x1^2 * x2^2 = 1 := by
          nlinarith [h6, sq_nonneg (x1 * x2), sq_nonneg (x1 * x2 - 1)]
        rw [h9]
        have h13 : x1^2 * x2^2 > 0 := by
          nlinarith [h10]
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith [h8, h10]
      linarith
    · -- k > 2
      have h1 : k ^ 2 > 4 := by nlinarith
      have h8 : x1 ^ 4 + x2 ^ 4 > 2 := by
        have h9 : x1 ^ 4 + x2 ^ 4 = ((x1^2 + x2^2) ^ 2) - 2 * (x1 * x2) ^ 2 := by
          ring
        have h10 : x1 ^ 2 + x2 ^ 2 = k ^ 2 - 2 := by
          nlinarith [h5, h6, sq_nonneg (x1 - x2), sq_nonneg (x1 + x2), sq_nonneg (k), sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)]
        rw [h10, h6] at h9
        nlinarith [h9, h1]
      have h7 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 > 2 := by
        have h9 : (x1 / x2) ^ 2 + (x2 / x1) ^ 2 = (x1^4 + x2^4) / (x1^2 * x2^2) := by
          field_simp [hx2_ne_zero, hx1_ne_zero]
          <;> ring
        have h10 : x1^2 * x2^2 = 1 := by
          nlinarith [h6, sq_nonneg (x1 * x2), sq_nonneg (x1 * x2 - 1)]
        rw [h9]
        have h13 : x1^2 * x2^2 > 0 := by
          nlinarith [h10]
        apply (lt_div_iff₀ (by positivity)).mpr
        nlinarith [h8, h10]
      linarith