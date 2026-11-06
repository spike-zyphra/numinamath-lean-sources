import Mathlib

theorem number_theory_242 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1 98 ∧ ∃ a b, a^2 - b^2 = n} = 73 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1 98 ∧ ∃ a b, a^2 - b^2 = n} = Finset.filter (fun n : ℕ => (n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3) ) (Finset.Icc 1 98) := by
    ext n
    simp
    intro h1 h2
    constructor
    · -- Assume ∃ a b, a^2 - b^2 = n
      rintro ⟨a, b, heq⟩
      have h3 : n < 99 := by omega
      have h5 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 := by
        by_contra h
        push_neg at h
        have h6 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by 
          have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
            omega
          rcases h1 with (h1 | h1 | h1 | h1) <;> simp [h1, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          <;> omega
        have h7 : b ^ 2 % 4 = 0 ∨ b ^ 2 % 4 = 1 := by 
          have h1 : b % 4 = 0 ∨ b % 4 = 1 ∨ b % 4 = 2 ∨ b % 4 = 3 := by 
            omega
          rcases h1 with (h1 | h1 | h1 | h1) <;> simp [h1, Nat.pow_mod, Nat.mul_mod, Nat.add_mod]
          <;> omega
        omega
      tauto
    · -- Assume n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 3 
      intro h
      rcases h with (h | h | h)
      · -- n % 4 = 0
        have h2 : n % 4 = 0 := h
        have h3 : ∃ k : ℕ, n = 4 * k := by 
          refine' ⟨n / 4, by omega⟩
        rcases h3 with ⟨k, hk⟩
        use k + 1, k - 1
        cases k with
        | zero => 
          omega  -- n = 0 not in range
        | succ k => 
          simp_all [Nat.pow_succ, Nat.mul_succ]
          <;> ring_nf 
          <;> omega 
      · -- n % 4 = 1
        have h2 : n % 4 = 1 := h
        have h3 : ∃ k : ℕ, n = 4 * k + 1 := by 
          refine' ⟨(n - 1) / 4, by omega⟩
        rcases h3 with ⟨k, hk⟩
        use 2 * k + 1, 2 * k
        all_goals
          try { 
            have hk' : n = 4 * k + 1 := hk
            all_goals 
              simp_all [Nat.pow_succ, Nat.mul_succ, Nat.pow_zero, Nat.mul_zero, Nat.pow_succ]
              <;> ring_nf 
              <;> omega 
          }
          <;> try { 
            simp_all [Nat.pow_succ, Nat.mul_succ, Nat.pow_zero, Nat.mul_zero, Nat.pow_succ]
            <;> ring_nf 
            <;> omega 
          }
          <;> try { nlinarith }
      · -- n % 4 = 3
        have h2 : n % 4 = 3 := h
        have h3 : ∃ k : ℕ, n = 4 * k + 3 := by 
          refine' ⟨(n - 3) / 4, by omega⟩
        rcases h3 with ⟨k, hk⟩
        use 2 * k + 2, 2 * k + 1
        all_goals
          try { 
            have hk' : n = 4 * k + 3 := hk
            all_goals 
              simp_all [Nat.pow_succ, Nat.mul_succ, Nat.pow_zero, Nat.mul_zero, Nat.pow_succ]
              <;> ring_nf 
              <;> omega 
          }
          <;> try { 
            simp_all [Nat.pow_succ, Nat.mul_succ, Nat.pow_zero, Nat.mul_zero, Nat.pow_succ]
            <;> ring_nf 
            <;> omega 
          }
          <;> try { nlinarith }
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide