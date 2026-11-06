import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_149669 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b + c = 13) :
  IsLeast {x | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a + b + c = 13 ∧ x = (a^2 + b^3 + c^4 + 2019) / (10 * b + 123 * c + 26)} 4 := by

  constructor
  · -- First, show that 4 is in the set.
    use 4, 4, 5
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    all_goals norm_num
  · -- Show 4 is the least element in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h, hx⟩
    have h1 : (10 * b + 123 * c + 26) > 0 := by
      nlinarith
    have h2 : (a^2 + b^3 + c^4 + 2019) / (10 * b + 123 * c + 26) ≥ 4 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith [sq_nonneg (a - 4), sq_nonneg (b - 4), sq_nonneg (c - 5), sq_nonneg (a + b - 8),
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a^2 - 16), sq_nonneg (b^2 - 16), sq_nonneg (c^2 - 25)]
    linarith [h2, hx]