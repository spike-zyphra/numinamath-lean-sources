import Mathlib

theorem number_theory_236273 :
    (∃ n : ℕ, n^2 = 1^3 + 2^3) ∧
    (∃ n : ℕ, n^2 = 1^3 + 2^3 + 3^3) ∧
    (∃ n : ℕ, n^2 = 1^3 + 2^3 + 3^3 + 4^3) ∧
    (∃ n : ℕ, n^2 = 1^3 + 2^3 + 3^3 + 4^3 + 5^3) := by
  constructor
  · -- Show that 1^3 + 2^3 is a perfect square
    use 3
    all_goals norm_num
  constructor
  · -- Show that 1^3 + 2^3 + 3^3 is a perfect square
    use 6
    all_goals norm_num
  constructor
  · -- Show that 1^3 + 2^3 + 3^3 + 4^3 is a perfect square
    use 10
    all_goals norm_num
  · -- Show that 1^3 + 2^3 + 3^3 + 4^3 + 5^3 is a perfect square
    use 15
    all_goals norm_num