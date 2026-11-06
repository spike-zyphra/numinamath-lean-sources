import Mathlib

theorem number_theory_118953 :
    Set.ncard {x : ℕ | ∃ a b, a ≠ b ∧ Nat.lcm a b = 64 ∧ x = Nat.gcd a b} = 6 := by 
  have h1 : {x : ℕ | ∃ a b, a ≠ b ∧ Nat.lcm a b = 64 ∧ x = Nat.gcd a b} = {1, 2, 4, 8, 16, 32} := by 
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor 
    · -- First direction: if x in { ... }, then x in {1,2,4,8,16,32}
      rintro ⟨a, b, hneq, hlcm, hx⟩
      have h2 : a ∣ 64 := by 
        have h2 : a ∣ Nat.lcm a b := by 
          exact Nat.dvd_lcm_left a b 
        have h3 : Nat.lcm a b = 64 := by 
          exact hlcm 
        rw [h3] at h2 
        exact h2 
      have h3 : b ∣ 64 := by 
        have h3 : b ∣ Nat.lcm a b := by 
          exact Nat.dvd_lcm_right a b 
        have h4 : Nat.lcm a b = 64 := by 
          exact hlcm 
        rw [h4] at h3 
        exact h3 
      have h4 : a ≤ 64 := by 
        exact Nat.le_of_dvd (by norm_num) h2 
      have h5 : b ≤ 64 := by 
        exact Nat.le_of_dvd (by norm_num) h3 
      interval_cases a <;> interval_cases b 
      <;> norm_num [Nat.lcm, Nat.gcd] at hlcm hx ⊢ 
      <;> omega 
    · -- Now the reverse
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1 
        use 1, 64 
        all_goals norm_num 
      · -- x = 2 
        use 2, 64 
        all_goals norm_num 
      · -- x = 4 
        use 4, 64 
        all_goals norm_num 
      · -- x = 8 
        use 8, 64 
        all_goals norm_num 
      · -- x = 16 
        use 16, 64 
        all_goals norm_num 
      · -- x = 32 
        use 32, 64 
        all_goals norm_num
  rw [h1] 
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]