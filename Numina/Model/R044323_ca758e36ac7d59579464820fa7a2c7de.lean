import Mathlib

theorem number_theory_14804 :
    IsLeast {x : ℕ | 0 < x ∧ ∃ m n : ℤ, x = 2002 * m + 44444 * n} 2 := by 
  constructor
  · -- Show that 2 is in the set
    constructor
    · norm_num
    · -- Show existence of integers m and n such that 2 = 2002*m + 44444*n.
      use 111, -5
      all_goals norm_num
  · -- Show that 2 is the smallest
    intro x hx
    rcases hx with ⟨hx_pos, ⟨m, n, hx_eq⟩⟩
    have eq1 : (x : ℤ) = 2002 * m + 44444 * n := by
      exact_mod_cast hx_eq
    have eq2 : (x : ℤ) % 2 = 0 := by
      omega
    have hx_ge_2 : x ≥ 2 := by
      omega
    linarith