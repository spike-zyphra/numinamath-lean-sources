import Mathlib

open Real

theorem algebra_20628 :
    IsLeast {x : ℝ | ∃ a b c d : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ x = (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d)} 16 := by
  constructor
  · -- Show 16 is in the set
    use 1, 1, 1, 1
    norm_num
  · -- Show that any value in the set is at least 16
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    have h1 : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) ≥ 16 := by
      have h2 : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) - 16 ≥ 0 := by
        have h3 : (a + b + c + d) * (1 / a + 1 / b + 1 / c + 1 / d) - 16 =
            (a - b) ^ 2 / (a * b) + (a - c) ^ 2 / (a * c) + (a - d) ^ 2 / (a * d) + (b - c) ^ 2 / (b * c) + (b - d) ^ 2 / (b * d) + (c - d) ^ 2 / (c * d) := by
          field_simp
          ring
          <;> field_simp
          <;> ring
        rw [h3]
        have h4 : 0 < a * b := mul_pos ha hb
        have h5 : 0 < a * c := mul_pos ha hc
        have h6 : 0 < a * d := mul_pos ha hd
        have h7 : 0 < b * c := mul_pos hb hc
        have h8 : 0 < b * d := mul_pos hb hd
        have h9 : 0 < c * d := mul_pos hc hd
        positivity
      linarith
    have h4 : x ≥ 16 := by
      rw [hx]
      linarith [h1]
    linarith