import Mathlib

theorem algebra_297558 {x : ℝ} (hx : x ∈ Set.Ioo (3 * Real.pi) (3.5 * Real.pi)) (h : Real.tan x = 4) :
    x = 3 * Real.pi + Real.arctan 4 := by
  rcases hx with ⟨hx1, hx2⟩
  have h3 : x - 3 * Real.pi > 0 := by linarith
  have h4 : x - 3 * Real.pi < Real.pi / 2 := by
    nlinarith [Real.pi_pos]
  have htan : Real.tan (x - 3 * Real.pi) = 4 := by
    have htan1 : Real.tan (x - 3 * Real.pi) = Real.tan x := by
      rw [show x - 3 * Real.pi = x - (3 : ℤ) * Real.pi by ring]
      rw [Real.tan_sub_int_mul_pi]
      all_goals norm_num
    rw [htan1, h]
  have h5 : x - 3 * Real.pi = Real.arctan 4 := by
    have h6 : Real.tan (x - 3 * Real.pi) = 4 := htan
    have h7 : x - 3 * Real.pi > -Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have h8 : x - 3 * Real.pi < Real.pi / 2 := by
      nlinarith [Real.pi_pos]
    have h9 : x - 3 * Real.pi = Real.arctan (Real.tan (x - 3 * Real.pi)) := by
      rw [Real.arctan_tan]
      all_goals
        linarith [Real.pi_pos]
    rw [h6] at h9
    linarith
  linarith