import Mathlib

theorem number_theory_127091 (a : ℕ → ℕ) (ha : ∀ n, 0 < a n)
    (h1 : a 1 = 3) (h2 : ∀ n, a (n + 1) = a n + Nat.gcd (n + 1) (a n)) :
    ∃! k, 0 < k ∧ a k = 2 * k := by

  have h3 : a 1 = a 0 + Nat.gcd 1 (a 0) := by
    specialize h2 0
    simpa using h2

  have h4 : Nat.gcd 1 (a 0) = 1 := by
    simp

  have h5 : a 0 = 2 := by
    rw [h4] at h3
    rw [h1] at h3
    omega

  have h9 : ∀ (n : ℕ), a n = n + 2 := by
    intro n
    induction n with
    | zero => 
      exact h5
    | succ n ih =>
      have h10 : a (n + 1) = a n + Nat.gcd (n + 1) (a n) := by 
        specialize h2 n 
        simpa using h2
      rw [h10]
      rw [ih]
      have h11 : Nat.gcd (n + 1) ((n) + 2) = 1 := by
        have h14 : Nat.gcd (n + 1) (n + 2) = 1 := by
          have h12 : n + 2 = (n + 1) + 1 := by omega
          rw [h12]
          simp [Nat.gcd_comm]
        exact h14
      omega

  use 2
  constructor
  · -- Show that 2 satisfies the condition.
    constructor
    · -- Show that 0 < 2
      norm_num
    · -- Show that a 2 = 2 * 2
      have h11 : a 2 = 4 := by
        rw [h9 2]
        all_goals norm_num
      norm_num at h11 ⊢
      exact h11
  · -- Show that 2 is the only solution
    intro k hk
    rcases hk with ⟨hk0, hk1⟩
    have hk10 : a k = k + 2 := h9 k
    rw [hk10] at hk1
    have hk2 : k = 2 := by
      omega
    omega