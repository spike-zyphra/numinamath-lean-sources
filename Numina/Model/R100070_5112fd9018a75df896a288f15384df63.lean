import Mathlib

theorem inequalities_2118 (m : ℝ) (hm : 0 < m ∧ m < 1) : m < 1 / m := by 
  have h1 : 0 < m := hm.1
  have h2 : m < 1 := hm.2
  have h3 : m * m < 1 := by 
    nlinarith 
  have h4 : m < 1 / m := by 
    have h5 : m > 0 := h1
    have h6 : m * m < 1 := h3
    have h14 : m - 1 / m < 0 := by
      have h15 : m > 0 := h1
      have h16 : m * m < 1 := h3
      have h17 : m * m - 1 < 0 := by linarith
      have h18 : (m * m - 1) / m < 0 := by 
        apply div_neg_of_neg_of_pos
        linarith
        all_goals linarith
      have h19 : (m * m - 1) / m = m - 1 / m := by 
        field_simp [h15]
        <;> ring
      linarith
    linarith
  exact h4