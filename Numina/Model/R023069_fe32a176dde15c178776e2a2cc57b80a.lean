import Mathlib

theorem algebra_95819 (c : ℝ) :
    (∃ x y, x > 0 ∧ y > 0 ∧ x - y = 2 ∧ c * x + y = 3) ↔ c > -1 ∧ c < 3 / 2 := by
  constructor
  · -- Forward direction: if (x, y) is a solution in Quadrant I, then -1 < c < 3/2
    rintro ⟨x, y, hx, hy, h1, h2⟩
    have h3 : y = x - 2 := by linarith
    rw [h3] at h2
    have hx2 : x > 2 := by
      nlinarith
    have h4 : (c + 1) * x = 5 := by
      linarith
    constructor
    · -- Show c > -1
      nlinarith [h4, hx2]
    · -- Show c < 3/2
      nlinarith [h4, hx2]
  · -- Backward direction: if -1 < c < 3/2, then a solution exists in Quadrant I
    rintro ⟨hc1, hc2⟩
    have hc3 : c + 1 > 0 := by linarith
    use 5 / (c + 1)
    use (5 / (c + 1) - 2)
    constructor
    · -- Show x > 0
      apply div_pos
      norm_num
      all_goals linarith
    constructor
    · -- Show y > 0
      have h5 : 5 / (c + 1) > 2 := by
        apply (lt_div_iff₀ (by linarith)).mpr
        nlinarith
      linarith
    constructor
    · -- Show x - y = 2
      field_simp
      <;> linarith
    · -- Show c * x + y = 3
      field_simp
      <;> nlinarith