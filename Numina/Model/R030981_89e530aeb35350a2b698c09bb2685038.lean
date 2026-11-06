import Mathlib

theorem algebra_17054 : IsLeast {x : ℝ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧
    x = (a + b + c) * (1 / (a + b) + 1 / (a + c) + 1 / (b + c))} (9 / 2) := by
  constructor
  · -- Show 9/2 is in the set
    use 1, 1, 1
    norm_num
  · -- Show no value less than 9/2 is in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, hx⟩
    have h : (a + b + c) * (1 / (a + b) + 1 / (a + c) + 1 / (b + c)) ≥ 9 / 2 := by
      have h1 : 0 < (a + b) * (a + c) * (b + c) := by positivity
      have h2 : (a + b + c) * (1 / (a + b) + 1 / (a + c) + 1 / (b + c)) - 9 / 2 ≥ 0 := by
        have h3 : (a + b + c) * (1 / (a + b) + 1 / (a + c) + 1 / (b + c)) - 9 / 2 =
            (2 * (a + b + c) * ((a + c) * (b + c) + (a + b) * (b + c) + (a + b) * (a + c)) - 9 * (a + b) * (a + c) * (b + c)) / (2 * (a + b) * (a + c) * (b + c)) := by
          field_simp
          ring
        rw [h3]
        have h4 : 2 * (a + b + c) * ((a + c) * (b + c) + (a + b) * (b + c) + (a + b) * (a + c)) - 9 * (a + b) * (a + c) * (b + c) ≥ 0 := by
          nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
        have h5 : 2 * (a + b) * (a + c) * (b + c) > 0 := by positivity
        apply div_nonneg
        · linarith
        · positivity
      linarith
    linarith [h, hx]