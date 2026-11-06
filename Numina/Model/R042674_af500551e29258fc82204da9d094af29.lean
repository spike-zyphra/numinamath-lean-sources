import Mathlib

theorem algebra_117628 :
    IsLeast {x : ℝ | ∃ a b c d : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a + 2 * b = 1 ∧ c + 2 * d = 1 ∧ x = 1 / a + 1 / (b * c * d)} 25 := by
  constructor
  · -- Show 25 is achieved
    use 1 / 5, 2 / 5, 1 / 2, 1 / 4
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show 25 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, h1, h2, hx⟩
    have h3 : 0 < a * (b * c * d) := by
      have h3a : 0 < a := ha
      have h3b : 0 < b := hb
      have h3c : 0 < c := hc
      have h3d : 0 < d := hd
      have h4 : 0 < b * c := by 
        nlinarith 
      have h5 : 0 < b * c * d := by
        have h4a : 0 < b * c := by 
          nlinarith
        have h4b : 0 < d := by linarith 
        nlinarith
      have h4a : 0 < a * (b * c * d) := by 
        apply mul_pos 
        linarith 
        linarith 
      exact h4a 
    have h4 : 1 / a + 1 / (b * c * d) ≥ 25 := by
      have h5 : 0 < a * (b * c * d) := h3
      have h6 : 1 / a + 1 / (b * c * d) - 25 ≥ 0 := by
        have h7 : 1 / a + 1 / (b * c * d) - 25 = (b * c * d + a - 25 * a * (b * c * d)) / (a * (b * c * d)) := by 
          field_simp 
          all_goals ring 
        rw [h7] at *
        apply div_nonneg 
        nlinarith [ sq_nonneg (a - 1 / 5), sq_nonneg (b - 2 / 5), sq_nonneg (c - 1 / 2), sq_nonneg (d - 1 / 4), 
              sq_nonneg (a * b - 1 / 5 * (2 / 5)), sq_nonneg (a * c - 1 / 5 * (1 / 2)), sq_nonneg (a * d - 1 / 5 * (1 / 4)), 
              sq_nonneg (b * c - (2 / 5) * (1 / 2)), sq_nonneg (b * d - (2 / 5) * (1 / 4)), sq_nonneg (c * d - (1 / 2) * (1 / 4)), 
              h1, h2, mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, mul_pos hb hd, mul_pos hc hd ]
        positivity
      linarith
    linarith [ hx, h4 ]