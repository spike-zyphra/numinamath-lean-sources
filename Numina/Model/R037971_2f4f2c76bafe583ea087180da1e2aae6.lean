import Mathlib

def P_type_prime (q : ℕ) : Prop :=
  Nat.Prime q ∧ ∃ m, m^2 = q + 1

theorem number_theory_313197 :
    Set.ncard {q | P_type_prime q} = 1 := by
  have h1 : {q | P_type_prime q} = {3} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume h : P_type_prime q. Need to show q = 3.
      intro h
      rcases h with ⟨hq, ⟨m, hm⟩⟩
      have h2 : m > 0 := by
        by_contra h
        push_neg at h
        have h3 : m = 0 := by 
          omega
        rw [h3] at hm
        have h4 : q + 1 = 0 := by 
          nlinarith
        have h5 : q = 0 := by 
          omega
        rw [h5] at hq
        norm_num at hq
        all_goals try { contradiction }
        all_goals try { tauto }
        all_goals try { nlinarith }
      by_cases h4 : m ≥ 3
      · -- m >= 3
        have h5 : m - 1 ≥ 2 := by
          omega
        have h6 : m + 1 ≥ 4 := by 
          omega
        have h7 : q = (m - 1) * (m + 1) := by
          have h7a : m ^ 2 = q + 1 := hm
          have h7b : m ^ 2 - 1 = q := by
            omega
          have h8c : q = m^2 - 1 := by 
            omega
          have h7d : m ^ 2 - 1 = (m - 1) * (m + 1) := by 
            cases m with
            | zero => omega  -- contradicts m >= 3
            | succ n => 
              simp [Nat.mul_add, Nat.add_mul, Nat.pow_two]
              all_goals
                ring_nf
                <;> omega
          rw [h7d] at h8c
          omega
        rw [h7] at hq
        have h8 : ¬ Nat.Prime ((m - 1) * (m + 1)) := by
          apply Nat.not_prime_mul
          all_goals
            nlinarith
        contradiction
      · -- m < 3
        have h8 : m ≤ 2 := by
          omega
        have h11 : m = 1 ∨ m = 2 := by
          have h7 : m > 0 := h2
          omega
        rcases h11 with (h11 | h11)
        · -- m = 1, then q = 0, this is a contradiction.
          have h12 : m = 1 := by
            omega
          rw [h12] at hm
          have h13 : q = 0 := by
            nlinarith
          rw [h13] at hq
          norm_num at hq
        · -- m = 2, then q = 3
          have h14 : m = 2 := by
            omega
          rw [h14] at hm
          have h15 : q = 3 := by
            nlinarith
          tauto
    · -- Assume q = 3, prove h
      intro h
      rw [h]
      constructor
      · norm_num
      · use 2
        all_goals norm_num
  rw [h1]
  simp