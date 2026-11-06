import Mathlib

theorem number_theory_105648 (n : ℕ) (hn : 1 < n) :
    n + n.primeFactorsList.head! = 30 ↔ n = 25 ∨ n = 27 ∨ n = 28 :=
by
  constructor
  · -- Forward
    intro h
    have h8 : n ≤ 30 := by
      by_contra h9
      push_neg at h9
      have h10 : n > 30 := by linarith
      have h11 : n.primeFactorsList.head! ≥ 0 := by
        apply Nat.zero_le
      have h12 : n + n.primeFactorsList.head! > 30 := by
        omega
      omega
    interval_cases n <;> norm_num [Nat.primeFactorsList] at h ⊢
  · -- Backward
    rintro (r | r | r)
    · 
      rw [r]
      native_decide
    · 
      rw [r]
      native_decide
    · 
      rw [r]
      native_decide