import Mathlib

-- Find the smallest positive integer $n$ such that $107 n$ has the same last two digits as $n$.
theorem number_theory_608283 : (∀ n ∈ {n :ℤ | n > 0 ∧ 107 * n % 100 = n % 100} , 50 ≤ n) ∧ 50 ∈ {n :ℤ | n > 0 ∧ 107 * n % 100 = n % 100} := by
  constructor
  · -- Show that for all $n$ in the set, $n \geq 50$
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    omega
  · -- Show that 50 is in the set
    constructor
    · norm_num
    · norm_num