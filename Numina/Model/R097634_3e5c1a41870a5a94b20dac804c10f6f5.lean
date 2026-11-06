import Mathlib

theorem number_theory_258886 : ∃ n, n > 0 ∧ ∃ k, 2 * n = k ^ 2 ∧ ∃ m, 3 * n = m ^ 3 ∧ ∃ p, 5 * n = p ^ 5 := by 
  use 2 ^ 15 * 3 ^ 20 * 5 ^ 24
  constructor
  · -- Show n > 0
    norm_num
  · -- Show that there exists k such that 2 * n = k ^ 2
    use 2 ^ 8 * 3 ^ 10 * 5 ^ 12
    constructor
    · -- Show that 2 * n = k ^ 2
      norm_num
    · -- Show that there exists m such that 3 * n = m ^ 3
      use 2 ^ 5 * 3 ^ 7 * 5 ^ 8
      constructor
      · -- Show that 3 * n = m ^ 3
        norm_num
      · -- Show that there exists p such that 5 * n = p ^ 5
        use 2 ^ 3 * 3 ^ 4 * 5 ^ 5
        all_goals norm_num