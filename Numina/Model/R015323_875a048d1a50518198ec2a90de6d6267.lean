import Mathlib

def isFramed (n : ℕ) := ∃ k, n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) = k^2

theorem number_theory_243182 :
    Set.ncard {n | 10 ≤ n ∧ n < 100 ∧ isFramed n} = 8 := by
  have : {n | 10 ≤ n ∧ n < 100 ∧ isFramed n} = {29, 38, 47, 56, 65, 74, 83, 92} := by 
    ext n 
    simp [isFramed]
    constructor
    · -- First, show that if n in {n | 10 ≤ n ∧ n < 100 ∧ isFramed n}, then in {29, 38, ..., 92}
      rintro ⟨h10, h100, ⟨k, hk⟩⟩
      interval_cases n <;> norm_num [Nat.ofDigits] at hk ⊢ 
      <;> try { 
        have : k ≤ 32 := by nlinarith 
        interval_cases k <;> omega 
      }
      <;> tauto
    · -- Now the reverse direction 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 29 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 29 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 38 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 38 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 47 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 47 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 56 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 56 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 65 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 65 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 74 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 74 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 83 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 83 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
      · -- 92 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · -- Show 92 is framed 
          use 11 
          all_goals norm_num [Nat.ofDigits] 
  rw [this] 
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }