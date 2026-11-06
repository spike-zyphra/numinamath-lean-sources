import Mathlib

def isGood (n : ℕ) := 2020 % n = 22

theorem number_theory_100663 :
    Set.ncard {n | isGood n} = 10 := by
  have h1 : {n | isGood n} = {27, 37, 54, 74, 111, 222, 333, 666, 999, 1998} := by
    ext n
    simp [isGood]
    constructor
    · -- Assume 2020 % n = 22, prove n ∈ {27, 37, 54, 74, 111, 222, 333, 666, 999, 1998}
      intro h
      have h1 : n ≤ 2020 := by
        by_contra h'
        push_neg at h'
        have h2 : 2020 % n = 2020 := by
          rw [Nat.mod_eq_of_lt]
          linarith
        omega
      interval_cases n <;> omega
    · -- Assume n ∈ {27, 37, 54, 74, 111, 222, 333, 666, 999, 1998}, prove 2020 % n = 22
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        norm_num [Nat.mod_eq_of_lt]
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }