import Mathlib

theorem number_theory_15320 :
    IsLeast {n | ∃ x y : ℕ, x > 0 ∧ y > 0 ∧ x ≠ y ∧ x ∣ 36 ∧ y ∣ 36 ∧ ¬(x * y ∣ 36) ∧ n = x * y} 8 := by
  constructor
  · -- Show 8 is in the set. 
    use 2, 4
    all_goals norm_num 
  · -- Show no smaller element is in the set.
    intro n hn
    rcases hn with ⟨x, y, hx, hy, hneq, hxdvd, hydvd, hxyndvd, hneq'⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 36 := by
      have h1 : x ∣ 36 := by
        exact hxdvd
      have h2 : x ≤ 36 := by 
        exact Nat.le_of_dvd (show 0 < 36 by norm_num) h1
      linarith
    have h2 : y ≤ 36 := by
      have h1 : y ∣ 36 := by
        exact hydvd
      have h2 : y ≤ 36 := by 
        exact Nat.le_of_dvd (show 0 < 36 by norm_num) h1
      linarith
    have h3 : x * y < 8 := by linarith [hneq']
    interval_cases x <;> interval_cases y <;> norm_num [hneq'] at *
    all_goals contradiction
    all_goals omega