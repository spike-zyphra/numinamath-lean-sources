import Mathlib

theorem number_theory_162229 (n : ℕ) (h₀ : n ≠ 0) (h₁ : 100 % n = 4) (h₂ : 90 % n = 18) :
    n = 24 := by
  have h3 : n ≤ 100 := by
    by_contra h
    push_neg at h
    have h4 : n > 100 := h
    have h5 : 100 % n = 100 := by
      rw [Nat.mod_eq_of_lt]
      linarith
    linarith [h₁, h5]

  have h4 : n > 18 := by
    by_contra h
    push_neg at h
    have : n ≤ 18 := by linarith
    interval_cases n <;> norm_num at h₂
    all_goals omega

  interval_cases n <;> norm_num at h₁ h₂ ⊢ <;> try { tauto } <;> try { contradiction } <;> try { omega }