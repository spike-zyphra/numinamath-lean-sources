import Mathlib

theorem algebra_254044 :
    { (a, b, c) : ℝ × ℝ × ℝ |
        (0 < a ∧ 0 < b ∧ 0 < c) ∧
        (6 * a + 3 * b + 8 * c = 1) ∧
        (12 * a = 1) ∧
        (18 * b = 1) ∧
        (24 * c = 1)
    } =
    { (1 / 12, 1 / 18, 1 / 24) } := by
    ext ⟨a, b, c⟩
    simp
    constructor
    · -- Assume (a, b, c) satisfy the original conditions, prove it equals (1/12, 1/18, 1/24)
      rintro ⟨⟨ha, hb, hc⟩, h1, h2, h3, h4⟩
      have ha' : a = 1 / 12 := by
        linarith
      have hb' : b = 1 / 18 := by
        linarith
      have hc' : c = 1 / 24 := by
        linarith
      simp [ha', hb', hc']
    · -- Assume (a, b, c) = (1/12, 1/18, 1/24) prove it satisfies the original conditions
      rintro ⟨rfl, rfl, rfl⟩
      constructor
      · -- Show all variables are positive
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      constructor
      · norm_num
      · norm_num