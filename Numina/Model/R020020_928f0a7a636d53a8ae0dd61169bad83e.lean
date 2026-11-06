import Mathlib

theorem number_theory_115801 (d : ℕ) (hd : d > 1) (h1 : 1059 % d = 1417 % d) (h2 : 1417 % d = 2312 % d) :
    d = 179 := by
  have h4 : d ≤ 1417 := by
    by_contra h
    push_neg at h
    have h4 : 1059 % d = 1059 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    have h5 : 1417 % d = 1417 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    rw [h4] at h1
    rw [h5] at h1
    omega
  interval_cases d <;> norm_num at h1 h2 ⊢ <;> omega