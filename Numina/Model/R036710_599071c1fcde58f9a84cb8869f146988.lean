import Mathlib

theorem number_theory_59235 (n : ℕ) (hn : n > 0) :
    ∃ x y z : ℕ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x ^ 2 + y ^ 2 = z ^ n := by
  by_cases h : n % 2 = 0
  · -- Assume n is even. Then n = 2k for some k.
    have h1 : ∃ k, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    have hk1 : k > 0 := by 
      omega
    use 3 * (5 ^ (k - 1))
    use 4 * (5 ^ (k - 1))
    use 5
    constructor
    · -- Show x > 0.
      have h11 : (5 : ℕ) ^ (k - 1) > 0 := by
        apply Nat.pow_pos
        norm_num
      nlinarith
    constructor
    · -- Show y > 0.
      have h11 : (5 : ℕ) ^ (k - 1) > 0 := by
        apply Nat.pow_pos
        norm_num
      nlinarith
    constructor
    · -- Show z > 0.
      norm_num
    · -- Show x ^ 2 + y ^ 2 = z ^ n.
      rw [show n = 2 * k by omega]
      have eq1 : (3 * (5 ^ (k - 1)) : ℕ) ^ 2 + (4 * (5 ^ (k - 1)) : ℕ) ^ 2 = (5 : ℕ) ^ (2 * k) := by
        have eq2 : (3 * (5 ^ (k - 1)) : ℕ) ^ 2 + (4 * (5 ^ (k - 1)) : ℕ) ^ 2 = 
          (9 + 16) * ((5 ^ (k - 1)) ^ 2 : ℕ) := by
          ring_nf
        rw [eq2]
        have eq3 : (9 + 16 : ℕ) = 25 := by norm_num
        rw [eq3]
        have eq4 : (25 : ℕ) * ((5 ^ (k - 1)) ^ 2 : ℕ) = (5 : ℕ) ^ (2 * k) := by
          have eq5 : (25 : ℕ) * ((5 ^ (k - 1)) ^ 2 : ℕ) = (5 : ℕ) ^ 2 * ((5 ^ (k - 1)) ^ 2 : ℕ) := by 
            norm_num
          rw [eq5]
          have eq6 : (5 : ℕ) ^ 2 * ((5 ^ (k - 1)) ^ 2 : ℕ) = ((5 : ℕ) * (5 ^ (k - 1)) ) ^ 2 := by 
            ring_nf
          rw [eq6]
          have eq7 : (5 : ℕ) * (5 ^ (k - 1)) = (5 : ℕ) ^ k := by 
            cases k with
            | zero => linarith
            | succ k => 
              simp [pow_succ, pow_zero] at *
              <;> omega
          rw [eq7]
          all_goals ring_nf
          <;> omega
        exact_mod_cast eq4
      exact_mod_cast eq1
  · -- Assume n is odd. Then n = 2k + 1 for some k.
    have h1 : ∃ k, n = 2 * k + 1 := by
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    use 2 ^ k
    use 2 ^ k
    use 2
    constructor
    · -- Show x > 0.
      have h2 : k ≥ 0 := by
        omega
      have h3 : (2 : ℕ) ^ k > 0 := by
        apply Nat.pow_pos
        norm_num
      linarith
    constructor
    · -- Show y > 0.
      have h2 : k ≥ 0 := by
        omega
      have h3 : (2 : ℕ) ^ k > 0 := by
        apply Nat.pow_pos
        norm_num
      linarith
    constructor
    · -- Show z > 0.
      norm_num
    · -- Show x ^ 2 + y ^ 2 = z ^ n.
      rw [show n = 2 * k + 1 by omega]
      have eq1 : ((2 : ℕ) ^ k) ^ 2 + ((2 : ℕ) ^ k) ^ 2 = (2 : ℕ) ^ (2 * k + 1) := by
        have eq2 : ((2 : ℕ) ^ k) ^ 2 + ((2 : ℕ) ^ k) ^ 2 = 2 * ((2 : ℕ) ^ k) ^ 2 := by 
          ring
        have eq3 : 2 * ((2 : ℕ) ^ k) ^ 2 = 2 * ((2 : ℕ) ^ (2 * k)) := by
          have h8 : ((2 : ℕ) ^ k) ^ 2 = (2 : ℕ) ^ (2 * k) := by 
            ring_nf
          rw [h8]
        have eq4 : 2 * ((2 : ℕ) ^ (2 * k)) = (2 : ℕ) ^ (2 * k + 1) := by
          have h11 : (2 * k + 1 : ℕ) = (2 * k) + 1 := by ring
          have h12 : (2 : ℕ) ^ (2 * k + 1) = (2 : ℕ) ^ (2 * k) * (2 : ℕ) ^ 1 := by
            rw [h11]
            rw [pow_add]
          have h13 : (2 : ℕ) ^ 1 = 2 := by norm_num
          rw [h12, h13]
          all_goals ring_nf
        rw [eq2, eq3, eq4]
      exact_mod_cast eq1