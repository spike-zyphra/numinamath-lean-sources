import Mathlib

theorem number_theory_130073 (n : ℕ) :
    (Nat.digits 10 n).sum + n = 313 ↔ n = 296 ∨ n = 305 := by
  constructor
  · -- Forward direction: if (Nat.digits 10 n).sum + n = 313, then n = 296 or n = 305
    intro h
    have h2 : n ≤ 313 := by
      by_contra h2
      push_neg at h2
      have h3 : (Nat.digits 10 n).sum ≥ 0 := by
        apply Nat.zero_le
      have h4 : (Nat.digits 10 n).sum + n > 313 := by
        have h5 : n > 313 := h2
        omega
      linarith
    interval_cases n <;> norm_num at h ⊢ <;> tauto
  · -- Backward direction: if n = 296 or n = 305, then (Nat.digits 10 n).sum + n = 313
    rintro (rfl | rfl)
    all_goals norm_num