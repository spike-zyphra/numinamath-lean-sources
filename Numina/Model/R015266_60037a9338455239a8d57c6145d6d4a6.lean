import Mathlib

def isFullyDivisible (n : ℕ) : Prop :=
  (Nat.digits 10 n).all (fun d => n % d = 0) ∧
  (Nat.digits 10 n).length = 2 ∧
  (Nat.digits 10 n).toFinset.card = 2 ∧
  (Nat.digits 10 n).all (fun d => d ≠ 0)

theorem number_theory_175806 :
    Set.ncard {n | isFullyDivisible n} = 5 := by
  have h1 : {n | isFullyDivisible n} = {12, 15, 24, 36, 48} := by 
    ext n
    simp [isFullyDivisible, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is fully divisible
      intro h
      rcases h with ⟨hdiv, h2, hne, hne0⟩
      have h1 : n < 100 := by
        by_contra h
        push_neg at h
        have h6 : (Nat.digits 10 n).length > 2 := by
          have h7 : n >= 100 := by omega
          have h8 : (Nat.log 10 n) >= 2 := by
            apply Nat.le_log_of_pow_le (by norm_num) h7
          have h9 : (Nat.digits 10 n).length = Nat.log 10 n + 1 := by rw [Nat.digits_len]; all_goals linarith
          linarith
        omega
      interval_cases n <;> norm_num at hdiv h2 hne hne0 ⊢ <;> all_goals tauto
    · -- Show the numbers are fully divisible
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num