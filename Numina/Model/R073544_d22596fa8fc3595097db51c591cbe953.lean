import Mathlib

theorem algebra_22147 : IsLeast {z : ℝ | ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + 2 * b = 1 ∧ z = 2 / a + 1 / b} 8 := by
  constructor
  · -- Show that 8 belongs to the set
    use 1 / 2, 1 / 4
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that any element in the set is ≥ 8
    intro z hz
    rcases hz with ⟨a, b, ha, hb, h1, h2⟩
    have h21 : a * b ≤ 1 / 8 := by
      nlinarith [sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 4), h1, mul_pos ha hb
      ]
    have h22 : 2 / a + 1 / b ≥ 8 := by
      have h23 : 2 / a + 1 / b = (a + 2 * b) / (a * b) := by
        field_simp
        <;> ring
      rw [h23]
      have h24 : 0 < a * b := mul_pos ha hb
      have h25 : (a + 2 * b) / (a * b) = 1 / (a * b) := by
        field_simp [show a * b ≠ 0 by positivity]
        all_goals
          nlinarith
      rw [h25]
      have h28 : 1 / (a * b) ≥ 8 := by
        have h29 : 0 < a * b := mul_pos ha hb
        have h30 : a * b ≤ 1 / 8 := h21
        -- Note: We need to express 1 / (1 / 8) = 8 explicitly
        have h31 : 1 / (a * b) ≥ 8 := by
          have h28a : a * b ≤ 1 / 8 := h30
          have h28b : 0 < a * b := h29
          have h32 : 1 / (a * b) ≥ 1 / (1 / 8) := by
            apply (div_le_div_iff (by positivity) (by positivity)).mpr
            nlinarith
          have h33 : (1 : ℝ) / (1 / 8) = 8 := by
            field_simp
            <;> norm_num
          linarith [h32, h33]
        exact h31
      nlinarith [h28, h21
      ]
    linarith [h22, h2
    ]