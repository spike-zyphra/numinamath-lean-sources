import Mathlib

theorem number_theory_78 {n : ℤ} (hn : ∀ m, n ∣ m) :
    n = 1 ∨ n = -1 := by
  have h1 := hn 1
  have h5 : n ≤ 1 := by
    apply Int.le_of_dvd (by norm_num) h1
  have h6 : -1 ≤ n := by
    have h7 : -n ∣ 1 := by
      exact Int.neg_dvd.2 h1
    have h8 : -n ≤ 1 := by
      apply Int.le_of_dvd (by norm_num) h7
    linarith
  interval_cases n <;> norm_num at h1 ⊢ <;> tauto