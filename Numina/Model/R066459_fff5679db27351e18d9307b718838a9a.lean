import Mathlib

theorem algebra_195558 :
    IsGreatest {x | ∃ a b c d : ℝ, a ∈ Set.Icc (-4) 4 ∧ b ∈ Set.Icc (-4) 4 ∧ c ∈ Set.Icc (-4) 4 ∧ d ∈ Set.Icc (-4) 4 ∧ x = a + 2 * b + c + 2 * d - a * b - b * c - c * d - d * a} 72 := by
  constructor
  · -- Show 72 is in the set
    use -4, 4, -4, 4
    constructor
    · -- Show -4 in interval
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 4 in interval
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show -4 in interval
      exact ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 4 in interval
      exact ⟨by norm_num, by norm_num⟩
    · -- Verify expression value
      norm_num
  · -- Show that 72 is the greatest element
    intro x hx
    rcases hx with ⟨a, b, c, d, ha, hb, hc, hd, hx⟩
    rcases ha with ⟨ha1, ha2⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hc with ⟨hc1, hc2⟩
    rcases hd with ⟨hd1, hd2⟩
    nlinarith [sq_nonneg (a + 4), sq_nonneg (b - 4), sq_nonneg (c + 4), sq_nonneg (d - 4),
      sq_nonneg (a - c), sq_nonneg (b - d),
      mul_nonneg (show (0 : ℝ) ≤ (4 - a) by nlinarith) (show (0 : ℝ) ≤ (4 - b) by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ (4 - b) by nlinarith) (show (0 : ℝ) ≤ (4 - c) by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ (4 - c) by nlinarith) (show (0 : ℝ) ≤ (4 - d) by nlinarith),
      mul_nonneg (show (0 : ℝ) ≤ (4 - d) by nlinarith) (show (0 : ℝ) ≤ (4 - a) by nlinarith)]