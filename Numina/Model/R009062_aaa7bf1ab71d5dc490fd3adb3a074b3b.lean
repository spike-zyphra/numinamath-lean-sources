import Mathlib

open Real Set

theorem algebra_21416 :
    IsLeast {r : ℝ | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 1 ∧ r = a ^ 2 + 2 * b ^ 2 + c ^ 2} (2 / 5) := by 
  constructor
  · -- Show that 2/5 can be achieved, i.e., exists a,b,c > 0 such that a + b + c = 1 and 2/5 = a^2 + 2b^2 + c^2
    use 2 / 5, 1 / 5, 2 / 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
  · -- Show that 2/5 is the least. For all r in the set, 2/5 ≤ r
    intro r hr
    rcases hr with ⟨a, b, c, ha, hb, hc, h1, hr⟩
    nlinarith [sq_nonneg (a - 2 / 5), sq_nonneg (b - 1 / 5), sq_nonneg (c - 2 / 5),
      h1, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]