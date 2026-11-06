import Mathlib

theorem number_theory_38459 (x : ℕ) (hx : x > 0) (h1 : 203 % x = 13) (h2 : 298 % x = 13) :
    x = 19 ∨ x = 95 := by
  have h3 : x ≤ 203 := by
    by_contra h
    push_neg at h
    have h4 : 203 % x = 203 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    omega

  interval_cases x <;> norm_num at h1 h2 ⊢ <;> try { tauto }