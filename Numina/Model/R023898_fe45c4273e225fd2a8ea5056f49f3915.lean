import Mathlib

theorem number_theory_82150 :
    ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ ∃ m n p : ℕ,
      m^2 = x + y ∧ n^2 = x^2 + y^2 ∧ p^2 = x^3 + y^3 := by

  use 184
  use 345
  constructor
  · norm_num -- 184 > 0
  constructor
  · norm_num -- 345 > 0
  · use 23
    use 391
    use 6877
    all_goals norm_num