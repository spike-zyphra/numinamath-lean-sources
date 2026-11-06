import Mathlib

theorem algebra_10955 (d1 d2 w b : ℝ) (hpos : 0 < d1 ∧ 0 < d2 ∧ 0 < w ∧ 0 < b)
    (hwb : b = 7 * w) (h : d1 / w = d2 / w + (d1 + d2) / b) :
    d2 / d1 = 3 / 4 := by 
  rcases hpos with ⟨hd1, hd2, hw, hb⟩
  have hw_ne : w ≠ 0 := by linarith 
  have hb_ne : b ≠ 0 := by linarith 
  have eq1 : d1 * b = d2 * b + (d1 + d2) * w := by 
    have eq2 : d1 / w = d2 / w + (d1 + d2) / b := h 
    field_simp [hw_ne, hb_ne] at eq2 ⊢ 
    nlinarith 
  have eq2 : d2 / d1 = 3 / 4 := by 
    have eq3 : d1 * (b - w) = d2 * (b + w) := by 
      nlinarith 
    have hw_eq : w ≠ 0 := by linarith 
    have hd1_ne : d1 ≠ 0 := by linarith 
    have h3 : b = 7 * w := by linarith [hwb] 
    have eq5 : 6 * d1 * w = 8 * w * d2 := by 
      have eq6 : d1 * (b - w) = d2 * (b + w) := eq3 
      rw [show b = 7 * w by linarith [h3] ] at eq6
      nlinarith 
    have eq6 : 6 * d1 = 8 * d2 := by 
      apply (mul_left_inj' hw_eq).mp 
      linarith 
    have eq7 : 3 * d1 = 4 * d2 := by 
      linarith 
    have eq8 : d2 / d1 = 3 / 4 := by 
      field_simp [hd1_ne]
      nlinarith 
    exact eq8 
  exact eq2