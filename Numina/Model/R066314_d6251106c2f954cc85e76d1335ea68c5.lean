import Mathlib

theorem number_theory_3171 :
    IsLeast {n | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ 23 * x - 7 * y = 2020 ∧ x + y = n} 110 := by 
  constructor
  · -- Show that (93, 17) satisfies the equation and yields 110.
    use 93, 17
    all_goals omega
  · -- Show that 110 is indeed the smallest such value.
    intro n hn
    rcases hn with ⟨x, y, hx, hy, h_eq, hn_eq⟩
    omega