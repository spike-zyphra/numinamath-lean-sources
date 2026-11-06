import Mathlib

set_option maxHeartbeats 400000

theorem algebra_609358: IsGreatest {m: ℝ | ∃ a b c: ℝ, 0 < a ∧ a ≤ b ∧ b ≤ c ∧ a + b + c = 10 
∧ a * b + b * c + c * a = 25 ∧ m = min (min (a * b) (b * c)) (c * a)} (25 / 9) := by
  constructor
  · -- Show that 25/9 is in the set
    use 5 / 3, 5 / 3, 20 / 3
    constructor
    · norm_num -- Show 0 < 5/3
    constructor
    · norm_num -- Show 5/3 ≤ 5/3
    constructor
    · norm_num -- Show 5/3 ≤ 20/3
    constructor
    · norm_num -- Show 5/3 + 5/3 + 20/3 = 10
    constructor
    · norm_num -- Show 5/3 * 5/3 + 5/3 * 20/3 + 20/3 * 5/3 = 25
    · -- Show 25/9 = min (min (5/3 * 5/3) (5/3 * 20/3)) (20/3 * 5/3)
      norm_num [min_eq_left_of_lt, min_eq_right]
  · -- Show that for any m in the set, m ≤ 25/9
    intro m hm
    rcases hm with ⟨a, b, c, ha, hab, hbc, h1, h2, hm⟩
    have h_eq1 : m = a * b := by 
      rw [hm]
      have h3 : c ≥ b := by linarith 
      have h4 : b ≥ a := by linarith 
      have h9 : a * b ≤ b * c := by 
        nlinarith [show 0 < c by nlinarith]
      have h10 : a * b ≤ c * a := by 
        nlinarith [show 0 < c by nlinarith]
      simp [min_eq_left_of_lt, min_eq_right, h9, h10]
      all_goals linarith 
    have h_eq2 : a * b ≤ 25 / 9 := by
      nlinarith [sq_nonneg (a - b), sq_nonneg (a - 5 / 3), sq_nonneg (b - 5 / 3), sq_nonneg ((10 - a - b) - 20 / 3), mul_pos ha (show 0 < b by nlinarith), mul_pos ha (show 0 < (10 - a - b) by nlinarith)]
    linarith [h_eq1, h_eq2]