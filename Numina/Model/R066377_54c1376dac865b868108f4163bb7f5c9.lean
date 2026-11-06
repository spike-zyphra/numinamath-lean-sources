import Mathlib

theorem number_theory_267287 : ∃ n, n ∈ {x | ∃ k, x = 11 * k + 3} ∧ n = 113 := by
  use 113
  constructor
  · -- Show that 113 belongs to the set
    use 10
    all_goals norm_num
  · -- Trivial equality
    rfl