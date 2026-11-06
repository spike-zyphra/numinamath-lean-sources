import Mathlib

theorem number_theory_230214 (n : ℕ) (h₀ : 25 % n + 38 % n + 43 % n = 18) :
    n = 11 := by
  have h1 : n ≤ 43 := by
    by_contra h
    push_neg at h
    have h2 : n > 43 := h
    have h3 : 25 % n = 25 := by
      rw [Nat.mod_eq_of_lt]
      omega
    have h4 : 38 % n = 38 := by
      rw [Nat.mod_eq_of_lt]
      omega
    have h5 : 43 % n = 43 := by
      rw [Nat.mod_eq_of_lt]
      omega
    rw [h3, h4, h5] at h₀
    all_goals omega
  interval_cases n <;> omega