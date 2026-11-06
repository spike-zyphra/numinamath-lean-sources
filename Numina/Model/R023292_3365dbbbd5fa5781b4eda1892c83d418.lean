import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_219847 :
  IsGreatest {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ abs (5 * x + y) + abs (5 * x - y) = 20} 124 ∧
  IsLeast {t : ℝ | ∃ x y, t = x^2 - x * y + y^2 ∧ abs (5 * x + y) + abs (5 * x - y) = 20} 3 := by 
  constructor
  · -- Show that 124 is greatest
    constructor 
    · -- Show that 124 is in the set
      use -2, 10
      norm_num [abs]
    · -- Show that for any t in the set, t <= 124
      intro t ht
      rcases ht with ⟨x, y, ht_eq, h_eq⟩ 
      have h1 : x^2 - x * y + y^2 ≤ 124 := by 
        cases' abs_cases (5 * x + y) with h1 h1 <;> cases' abs_cases (5 * x - y) with h2 h2 
        <;> try { 
            nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (y + 1)
          ]
        }
      linarith 
  · -- Show that 3 is least
    constructor 
    · -- Show that 3 is in the set
      use 2, 1
      norm_num [abs]
    · -- Show that for any t in the set, 3 <= t
      intro t ht
      rcases ht with ⟨x, y, ht_eq, h_eq⟩ 
      have h2 : x^2 - x * y + y^2 ≥ 3 := by 
        cases' abs_cases (5 * x + y) with h1 h1 <;> cases' abs_cases (5 * x - y) with h2 h2 
        <;> try { 
            nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2), sq_nonneg (y - 10), sq_nonneg (y + 10), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (x - 2), sq_nonneg (y + 1)
          ]
        }
      linarith