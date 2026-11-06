import Mathlib

theorem algebra_96891 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (a b : ℝ)
    (ha : 0 < a) (hb : 0 < b) (h : a > b) (h1 : Real.tan x = 2 * a * b / (a ^ 2 - b ^ 2)) :
    Real.sin x = 2 * a * b / (a ^ 2 + b ^ 2) := by
  rcases hx with ⟨hx1, hx2⟩
  have h2 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [show Real.pi > 0 by exact Real.pi_pos, hx1, hx2]
    linarith [show Real.pi > 0 by exact Real.pi_pos, hx1, hx2]
  have h3 : Real.cos x > 0 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    linarith [show Real.pi > 0 by exact Real.pi_pos, hx1, hx2]
    linarith [show Real.pi > 0 by exact Real.pi_pos, hx1, hx2]
  have h4 : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  have h5 : Real.sin x / Real.cos x = 2 * a * b / (a ^ 2 - b ^ 2) := by 
    rw [h1] at h4
    linarith
  have h6 : Real.sin x = 2 * a * b / (a ^ 2 - b ^ 2) * Real.cos x := by
    have h7 : Real.cos x ≠ 0 := by linarith
    field_simp [h7] at h5 ⊢
    linarith
  have h7 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h8 : Real.cos x = ( (a ^ 2 - b ^ 2) / (2 * a * b) ) * Real.sin x := by 
    have h9 : Real.sin x = 2 * a * b / (a ^ 2 - b ^ 2) * Real.cos x := h6
    have h10 : Real.cos x ≠ 0 := by linarith
    have h11 : (a ^ 2 - b ^ 2) ≠ 0 := by
      nlinarith [h, sq_pos_of_pos ha, sq_pos_of_pos hb]
    have : Real.sin x ≠ 0 := by linarith [h2]
    field_simp [h2] at h9 ⊢
    <;> nlinarith
  have h9 : Real.sin x ^ 2 = (2 * a * b / (a ^ 2 + b ^ 2)) ^ 2 := by
    rw [h8] at h7
    field_simp [(show (a ^ 2 - b ^ 2) ≠ 0 by nlinarith [h, sq_pos_of_pos ha, sq_pos_of_pos hb]), 
      (show (a ^ 2 + b ^ 2) ≠ 0 by nlinarith [h, sq_pos_of_pos ha, sq_pos_of_pos hb]
        )] at h7 ⊢
    nlinarith [sq_nonneg (a ^ 2 - b ^ 2), sq_nonneg (a ^ 2 + b ^ 2), sq_pos_of_pos ha, sq_pos_of_pos hb, mul_pos ha hb, Real.sin_sq_le_one x
      ]
  have h11 : Real.sin x > 0 := h2
  have h12 : (2 * a * b / (a ^ 2 + b ^ 2) ) > 0 := by
    apply div_pos
    · -- Show that the numerator 2 * a * b is positive
      nlinarith [hb, ha, h, mul_pos ha hb]
    · -- Show that the denominator a^2 + b^2 is positive
      nlinarith [hb, ha, h, sq_pos_of_pos ha, sq_nonneg (a ^ 2), sq_nonneg (b ^ 2), sq_pos_of_pos hb, h
      ]
  have h13 : Real.sin x = 2 * a * b / (a ^ 2 + b ^ 2) := by
    have h0 : Real.sin x ^ 2 = (2 * a * b / (a ^ 2 + b ^ 2)) ^ 2 := h9
    have h14 : Real.sin x > 0 := h2
    have h15 : (2 * a * b / (a ^ 2 + b ^ 2) ) > 0 := h12
    have h18 : Real.sin x = 2 * a * b / (a ^ 2 + b ^ 2) := by
      nlinarith [sq_nonneg (Real.sin x - 2 * a * b / (a ^ 2 + b ^ 2)), sq_nonneg (2 * a * b / (a ^ 2 + b ^ 2) - Real.sin x), h0, h14, h15
        ]
    linarith
  exact h13