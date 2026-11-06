import Mathlib

theorem number_theory_263683 (x : ℕ) (hx : x > 0) (h : 100 % x = 10) :
    1000 % x = 10 := by
  by_cases h1 : x ≤ 100
  · -- Case 1: if x ≤ 100.
    interval_cases x <;> norm_num at h ⊢ <;> omega
  · -- Case 2: if x > 100.
    have h2 : 100 % x = 10 := h
    have h3 : x ≥ 101 := by
      omega
    have h4 : 100 < x := by
      omega
    have h5 : 100 % x = 100 := by
      rw [Nat.mod_eq_of_lt]
      all_goals linarith
    rw [h5] at h
    all_goals omega