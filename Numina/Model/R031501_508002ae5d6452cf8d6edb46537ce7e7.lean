import Mathlib

theorem number_theory_15815 : {x : ℕ | ∃ p : ℕ, Nat.Prime p ∧ p > 5 ∧ x = p ^ 2 % 120}.encard = 2 := by
  have h1 : {x : ℕ | ∃ p : ℕ, Nat.Prime p ∧ p > 5 ∧ x = p ^ 2 % 120} = {1, 49} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in the left side, need to prove x in the right side
      intro h
      rcases h with ⟨p, hp, hp_gt, hx⟩
      have h2 : p % 2 = 1 := by
        by_contra h
        push_neg at h
        have h3 : p % 2 = 0 := by
          omega
        have h6 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega)
          all_goals omega
        contradiction
      have h3 : p % 3 = 1 ∨ p % 3 = 2 := by
        by_contra h
        push_neg at h
        have h4 : p % 3 = 0 := by
          omega
        have h9 : 3 ∣ p := by
          omega
        have h10 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt h9
          all_goals omega
        contradiction
      have h4 : p % 5 = 1 ∨ p % 5 = 2 ∨ p % 5 = 3 ∨ p % 5 = 4 := by
        by_contra h
        push_neg at h
        have h5 : p % 5 = 0 := by
          omega
        have h13 : 5 ∣ p := by
          omega
        have h14 : ¬ Nat.Prime p := by
          apply Nat.not_prime_of_dvd_of_lt h13
          all_goals omega
        contradiction
      have h5 : p ^ 2 % 8 = 1 := by
        have h1 : p % 2 = 1 := h2
        have h11 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by 
          omega
        rcases h11 with (h | h | h | h) <;> simp [Nat.pow_mod, h, Nat.mul_mod]
      have h6 : p ^ 2 % 3 = 1 := by
        rcases h3 with (h3 | h3) <;> simp [Nat.pow_mod, h3, Nat.mul_mod]
      have h7 : p ^ 2 % 5 = 1 ∨ p ^ 2 % 5 = 4 := by
        rcases h4 with (h4 | h4 | h4 | h4) <;> simp [Nat.pow_mod, h4, Nat.mul_mod]
      have h8 : p ^ 2 % 120 = 1 ∨ p ^ 2 % 120 = 49 := by
        omega
      rcases h8 with (h8 | h8)
      · -- x = 1
        omega
      · -- x = 49
        omega
    · -- Assume x in the right side, need to prove x in the left side
      rintro (rfl | rfl)
      · -- Show that 1 is in the set
        use 11
        all_goals norm_num
      · -- Show that 49 is in the set
        use 7
        all_goals norm_num
  rw [h1]
  rw [Set.encard_pair (by norm_num)]
  all_goals norm_num