import Mathlib

/-
Let $k$ be a positive integer. What is the remainder when $5^{6k}$ is divided by 7? Show the answer is 1.
-/

theorem number_theory_636861 (k : ℕ) (kpow: 0 < k):
5^(6*k) % 7 = 1 := by

  have cla : ∀ n : ℕ, 5^(6*n) % 7 = 1 ∧ 5^(6*n+1) % 7 = 5 ∧ 5^(6*n+2) % 7 = 4 ∧ 5^(6*n+3) % 7 = 6 ∧ 5^(6*n+4) % 7 = 2 ∧ 5^(6*n+5) % 7 = 3 := by
    intro n
    induction' n with n hn

    simp

    have h5 : 5 ^ (6 * n + 5) % 7 = 3 := by tauto

    have h6 : 5 ^ (6 * (n + 1)) % 7 = 1 := by 
      have : 5 ^ (6 * (n + 1)) = 5 ^ (6 * n + 5)*5 := by 
        have : 6 * (n + 1) = 6*n+5 + 1 := by ring
        rw [this]
        rw [pow_succ]
      rw [this]
      rw [Nat.mul_mod, h5]

    have h7 : 5 ^ (6 * (n + 1)+1) % 7 = 5 := by 
      rw [pow_succ]
      rw [Nat.mul_mod, h6]

    have h8 : 5 ^ (6 * (n + 1)+2) % 7 = 4 := by
      rw [pow_succ]
      rw [Nat.mul_mod, h7]

    have h9 : 5 ^ (6 * (n + 1)+3) % 7 = 6 := by
      rw [pow_succ]
      rw [Nat.mul_mod, h8]
      
    have h10 : 5 ^ (6 * (n + 1)+4) % 7= 2 := by 
      rw [pow_succ]
      rw [Nat.mul_mod, h9]
      
    have h11 : 5 ^ (6 * (n + 1)+5) % 7= 3 := by
      rw [pow_succ]
      rw [Nat.mul_mod, h10]
      
    ring_nf at h6 h7 h8 h9 h10 h11 ⊢
    constructor
    exact h6
    constructor
    exact h7
    constructor
    exact h8
    constructor
    exact h9
    constructor
    exact h10
    exact h11

  specialize cla k
  exact cla.left
  