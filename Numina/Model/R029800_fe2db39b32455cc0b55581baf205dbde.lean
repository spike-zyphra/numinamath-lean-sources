import Mathlib

theorem algebra_22471 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a / b + b / c + c / a = 7) (h2 : b / a + c / b + a / c = 9) :
    a ^ 3 / b ^ 3 + b ^ 3 / c ^ 3 + c ^ 3 / a ^ 3 = 157 := by
  have h3 : a^3 / b^3 + b^3 / c^3 + c^3 / a^3 = 
          (a / b + b / c + c / a) ^ 3 - 3 * (a / b + b / c + c / a) * ((a / b) * (b / c) + (b / c) * (c / a) + (c / a) * (a / b)) + 3 * ((a / b) * (b / c) * (c / a)) := by
    field_simp
    ring
  have h4 : (a / b) * (b / c) + (b / c) * (c / a) + (c / a) * (a / b) = 9 := by
    have h5 : (a / b) * (b / c) + (b / c) * (c / a) + (c / a) * (a / b) = (a / c + b / a + c / b) := by
      field_simp
      <;> ring
    have h6 : (a / c + b / a + c / b) = 9 := by
      have h7 : b / a + c / b + a / c = 9 := h2
      have h8 : a / c + b / a + c / b = b / a + c / b + a / c := by
        ring_nf
      linarith [h7, h8]
    linarith [h5, h6]
  have h5 : (a / b) * (b / c) * (c / a) = 1 := by
    field_simp
    <;> ring
  rw [h3, h1, h4, h5]
  all_goals norm_num