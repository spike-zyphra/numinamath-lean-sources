import Mathlib


theorem algebra_172715 {x : ℝ} (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℝ)
    (ha : 0 < b) (hb : b < a) (h : Real.tan x = 2 * a * b / (a ^ 2 - b ^ 2)) :
    Real.sin x = 2 * a * b / (a ^ 2 + b ^ 2) := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [Real.pi_pos, hx1, hx2]
    linarith [Real.pi_pos, hx1, hx2]

  have h2 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [Real.pi_pos, hx1, hx2]
    linarith [Real.pi_pos, hx1, hx2]

  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]

  rw [htan] at h

  have ha2b2_pos : a^2 - b^2 > 0 := by nlinarith [ha, hb]
  have ha2b2_ne0 : a^2 - b^2 ≠ 0 := by linarith

  have h3 : Real.sin x = (2 * a * b / (a^2 - b^2)) * Real.cos x := by
    have hne : a^2 - b^2 ≠ 0 := by linarith
    have h4 : Real.sin x = (2 * a * b / (a^2 - b^2)) * Real.cos x := by
      field_simp [hne] at h ⊢
      nlinarith [h, h1]
    exact h4

  have h4 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  rw [h3] at h4

  have h5 : Real.cos x ^ 2 = (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2 := by
    have h4' : ( (2 * a * b / (a ^ 2 - b ^ 2)) * Real.cos x ) ^ 2 + Real.cos x ^ 2 = 1 := by
      nlinarith [h4]

    have h5 : Real.cos x ^ 2 * ( ((2 * a * b) / (a^2 - b^2)) ^ 2 + 1 ) = 1 := by
      have h4' : ( (2 * a * b / (a ^ 2 - b ^ 2)) * Real.cos x ) ^ 2 + Real.cos x ^ 2 = 1 := by
        nlinarith [h4]
      nlinarith [h4']

    have h7 : Real.cos x ^ 2 = 1 / ( ((2 * a * b) / (a^2 - b^2)) ^ 2 + 1 ) := by
      have hne : (((2 * a * b) / (a^2 - b^2)) ^ 2 + 1 ) ≠ 0 := by
        positivity
      field_simp [hne] at h5 ⊢
      nlinarith [h5, hne]

    rw [h7]

    have h8 : ((2 * a * b) / (a^2 - b^2)) ^ 2 + 1 = (a ^ 2 + b ^ 2) ^ 2 / (a ^ 2 - b ^ 2) ^ 2 := by
      field_simp [show a ^ 2 - b ^ 2 ≠ 0 by linarith]
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a * b), sq_nonneg (a ^ 2 + b ^ 2)]

    rw [h8]

    have h9 : (a ^ 2 + b ^ 2) ^ 2 ≠ 0 := by
      positivity
    have h10 : (a ^ 2 - b ^ 2) ^ 2 ≠ 0 := by
      intro h0
      have : a ^ 2 - b ^ 2 = 0 := by
        nlinarith [pow_eq_zero h0]
      linarith

    field_simp [h9, h10]
    <;> nlinarith

  have h6 : Real.cos x = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) := by
    have h7 : Real.cos x > 0 := h1
    have h8 : Real.cos x = Real.sqrt (Real.cos x ^ 2) := by
      rw [Real.sqrt_sq (show 0 ≤ Real.cos x by linarith)]
    rw [h8, h5]

    have ha2b2_pos : a ^ 2 - b ^ 2 > 0 := by nlinarith [ha, hb]
    have ha2b2_nonneg : 0 ≤ a ^ 2 - b ^ 2 := by linarith
    have h9 : Real.sqrt ((a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2) = (a ^ 2 - b ^ 2) / (a ^ 2 + b ^ 2) := by
      have h10 : Real.sqrt ((a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2) = Real.sqrt ((a ^ 2 - b ^ 2) ^ 2) / Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) := by
        field_simp [Real.sqrt_div]
      have h11 : Real.sqrt ((a ^ 2 - b ^ 2) ^ 2) = a ^ 2 - b ^ 2 := by
        rw [Real.sqrt_sq (show 0 ≤ a ^ 2 - b ^ 2 by linarith)]
      have h12 : Real.sqrt ((a ^ 2 + b ^ 2) ^ 2) = a ^ 2 + b ^ 2 := by
        rw [Real.sqrt_sq (show 0 ≤ a ^ 2 + b ^ 2 by nlinarith)]
      rw [h10, h11, h12]
    linarith [h9]

  have h7 : Real.sin x = 2 * a * b / (a ^ 2 + b ^ 2) := by
    rw [h3, h6]
    have hne : a ^ 2 - b ^ 2 ≠ 0 := by linarith
    field_simp [hne]
    <;> nlinarith [sq_pos_of_pos (show 0 < a ^ 2 - b ^ 2 by nlinarith), sq_pos_of_pos (show 0 < a ^ 2 + b ^ 2 by nlinarith)]

  exact h7