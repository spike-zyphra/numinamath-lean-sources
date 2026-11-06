import Mathlib

theorem algebra_6118 (x : ℝ) (hx : x ∈ Set.Ioo 0 (Real.pi / 2)) (h : Real.cos x = 7 / 13) :
    Real.tan x - Real.sin x = 12 * Real.sqrt 30 / 91 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : Real.sin x > 0 := by
    apply Real.sin_pos_of_pos_of_lt_pi
    linarith [hx1, Real.pi_pos]
    linarith [hx2, Real.pi_pos]
  have h2 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h] at h2
  have h3 : Real.sin x ^ 2 = 120 / 169 := by linarith
  have h4 : Real.sin x = 2 * Real.sqrt 30 / 13 := by
    have h5 : Real.sin x = Real.sqrt (Real.sin x ^ 2) := by
      rw [Real.sqrt_sq]
      all_goals nlinarith
    rw [h5, h3]
    have h7 : Real.sqrt (120 / 169) = Real.sqrt 120 / 13 := by
      rw [show (120 / 169 : ℝ) = (120 : ℝ) / (13 ^ 2) by ring]
      field_simp [Real.sqrt_div, Real.sqrt_sq]
    have h8 : Real.sqrt 120 = 2 * Real.sqrt 30 := by
      rw [show (120 : ℝ) = 4 * 30 by norm_num]
      rw [Real.sqrt_mul (by norm_num)]
      have h9 : Real.sqrt (4 : ℝ) = 2 := by
        rw [Real.sqrt_eq_cases]
        norm_num
      rw [h9]
      all_goals ring_nf <;> norm_num
    rw [h7, h8]
    all_goals nlinarith
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan, h4, h]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring