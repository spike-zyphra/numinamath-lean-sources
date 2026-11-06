import Mathlib

theorem algebra_21205 :
    IsLeast {x : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = ((a + b) * (a + c) * (b + c)) / (a * b * c)} 8 := by
  constructor
  · -- First part: Prove that 8 is in the set
    use 1, 1, 1
    norm_num
  · -- Second part: Prove that 8 is a lower bound
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h_eq⟩
    have h1 : (a + b) * (a + c) * (b + c) ≥ 8 * (a * b * c) := by
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
        sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
        sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
    have h2 : ((a + b) * (a + c) * (b + c)) / (a * b * c) ≥ 8 := by
      have pos1 : a * b * c > 0 := mul_pos (mul_pos ha hb) hc
      apply (le_div_iff₀ pos1).mpr
      nlinarith [h1]
    linarith [h_eq, h2]