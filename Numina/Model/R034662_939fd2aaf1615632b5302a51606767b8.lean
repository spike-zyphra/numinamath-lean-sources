import Mathlib


theorem number_theory_16132 :
    Set.ncard {x : ℕ | ∃ a b, x = Nat.gcd a b ∧ x * Nat.lcm a b = 200} = 4 := by
  have h1 : {x : ℕ | ∃ a b, x = Nat.gcd a b ∧ x * Nat.lcm a b = 200} = {1, 2, 5, 10} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Assume x in the left side, prove x in {1,2,5,10}
      rintro ⟨a, b, h_eq, h_eq2⟩
      have h3 : x ^ 2 ∣ 200 := by
        have h9 : x ∣ a := by
          have : x = Nat.gcd a b := by
            omega
          rw [this]
          exact Nat.gcd_dvd_left a b
        have h10 : x ∣ b := by
          have : x = Nat.gcd a b := by
            omega
          rw [this]
          exact Nat.gcd_dvd_right a b
        have h11 : x ^ 2 ∣ a * b := by
          have h12 : x ∣ a := h9
          have h13 : x ∣ b := h10
          have h14 : x * x ∣ a * b := by
            apply Nat.mul_dvd_mul
            exact h12
            exact h13
          ring_nf at h14 ⊢
          exact h14
        have h12 : x * (Nat.lcm a b) = a * b := by
          have h13 : x = Nat.gcd a b := by
            omega
          rw [h13]
          rw [Nat.gcd_mul_lcm a b]
        have h13 : x ^ 2 ∣ x * (Nat.lcm a b) := by
          rw [show x * (Nat.lcm a b) = a * b by linarith [h12]] 
          exact h11
        have h14 : x ^ 2 ∣ 200 := by
          have h15 : x * (Nat.lcm a b) = 200 := by
            linarith [h_eq2]
          rw [show x * (Nat.lcm a b) = 200 by linarith [h15]] at h13
          exact h13
        exact h14
      have h4 : x ≤ 14 := by
        have h11 : x ^ 2 ≤ 200 := by
          exact Nat.le_of_dvd (by norm_num) h3
        have h4 : x ≤ 14 := by
          nlinarith
        exact h4
      interval_cases x <;> norm_num at h3 h4 h_eq2 ⊢
    · -- Assume x in {1,2,5,10}, prove x in the left side
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        use 1, 200
        all_goals norm_num
      · -- x = 2
        use 2, 100
        all_goals norm_num
      · -- x = 5
        use 5, 40
        all_goals norm_num
      · -- x = 10
        use 10, 20
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]