import Mathlib

theorem number_theory_6378 :
    IsGreatest {x | ∃ m n, m > 0 ∧ n > 0 ∧ m + n = 36 ∧ x = Nat.lcm m n} 323 := by
  constructor
  · -- Show that 323 is in the set
    use 17, 19
    all_goals norm_num
  · -- Show that 323 is the greatest element in the set
    intro x hx
    rcases hx with ⟨m, n, hm, hn, h_sum, hx_eq⟩
    have h1 : m ≤ 36 := by omega
    have h2 : n = 36 - m := by omega 
    interval_cases m <;> norm_num [h2, hx_eq] at *