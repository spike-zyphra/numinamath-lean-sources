import Mathlib

theorem number_theory_255270 (n : ℕ) (h₀ : n ≠ 0) (h₁ : 1270 / n = 74) :
    n = 17 ∧ 1270 % n = 12 := by
  have h2 : n ≤ 1270 := by
    by_contra h
    push_neg at h
    have h3 : 1270 / n = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    omega
  interval_cases n <;> norm_num at h₁ ⊢ <;> tauto