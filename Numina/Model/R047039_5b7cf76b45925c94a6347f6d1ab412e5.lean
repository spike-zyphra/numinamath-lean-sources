import Mathlib


theorem algebra_20928 :
    IsGreatest { x:ℝ|∃a b :ℝ  , (-6 ≤ a ∧ a ≤ -2 ) ∧ (3 ≤ b ∧ b ≤ 5) ∧ x = (a + 1 / b) * (1 / b - a) } (-35 / 9) := by
  constructor
  · -- Show that -35/9 is in the set.
    use -2, 3
    norm_num
  · -- Show that -35/9 is greatest in the set.
    intro x hx
    rcases hx with ⟨a, b, ⟨h1, h2⟩, ⟨h3, h4⟩, heq⟩
    have h5 : (a + 1 / b) * (1 / b - a) = 1 / (b^2) - a^2 := by
      field_simp
      <;> ring
    have h6 : (a + 1 / b) * (1 / b - a) ≤ -35 / 9 := by
      have h13 : (1 / (b ^ 2) ) ≤ 1 / 9 := by
        have h14 : b ^ 2 ≥ 9 := by
          nlinarith
        have h15 : (1 / (b ^ 2) ) ≤ (1 / (9: ℝ)) := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        linarith
      have h14 : a^2 ≥ 4 := by
        nlinarith
      have h15 : 1 / (b ^ 2) + 35 / 9 ≤ 4 := by
        have h11 : (1 / (b ^ 2) ) ≤ 1 / 9 := h13
        linarith
      have h16 : 1 / (b ^ 2) + 35 / 9 ≤ a ^ 2 := by
        linarith
      linarith [h5, h16]
    linarith [heq, h6]