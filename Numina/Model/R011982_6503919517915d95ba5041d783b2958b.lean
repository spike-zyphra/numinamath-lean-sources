import Mathlib

theorem number_theory_68778 : {n | (Nat.digits 10 n).length = 3 ∧ ((Nat.digits 10 n).map (λ x => x ^ 2)).sum ∣ 26} = {100, 101, 110, 320, 302, 230, 203, 510, 501, 150, 105, 431, 413, 314, 341, 143, 134} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume (Nat.digits 10 n).length = 3 ∧ ((Nat.digits 10 n).map (λ x => x ^ 2)).sum ∣ 26, prove the disjunction
    intro h 
    rcases h with ⟨h1, h2⟩
    have h3 : n ≤ 999 := by
      by_contra h
      push_neg at h
      have h5 : (Nat.digits 10 n).length > 3 := by 
        have h6 : Nat.log 10 n ≥ 3 := by 
          have : 10 ^ 3 ≤ n := by linarith
          exact Nat.le_log_of_pow_le (by linarith) this 
        have h8 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by
          rw [Nat.digits_len]
          all_goals omega 
        omega 
      omega 
    have h4 : n ≥ 100 := by 
      by_contra h 
      push_neg at h 
      interval_cases n <;> norm_num at h1 h2 
    interval_cases n <;> norm_num at h1 h2 ⊢ 
  · -- Show that each of these elements in the explicit set indeed has 3 digits and sum of squares divides 26.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals 
      constructor <;> norm_num