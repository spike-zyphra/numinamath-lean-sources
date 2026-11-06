import Mathlib

theorem number_theory_15841 :
    IsGreatest {x | ∃ n, x = n^2 ∧ x ∣ 1512} 36 := by 
  constructor
  · -- Show that 36 is obtained.
    use 6
    all_goals norm_num
  · -- Show that any number in the set is ≤ 36.
    intro x hx
    rcases hx with ⟨n, rfl, hn⟩
    have h1 : n ^ 2 ∣ 1512 := hn
    have h2 : n ≤ 38 := by nlinarith [show n ^ 2 ≤ 1512 by exact Nat.le_of_dvd (by linarith) h1]
    interval_cases n <;> norm_num at *
    all_goals omega