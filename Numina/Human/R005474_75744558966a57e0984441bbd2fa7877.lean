import Mathlib
/- Find the number of distinct primes dividing $1 \cdot 2 \cdot 3 \cdots 9 \cdot 10$. -/
theorem number_theory_608430 : {p : ℕ | p.Prime ∧ p ∣ Nat.factorial 10}.ncard = 4:= by
  -- First, we prove that if a prime p divides (n+1)!, then p ≤ (n+1)
  have h1 : ∀ p : ℕ, Nat.Prime p → (∀ n : ℕ, p ∣ Nat.factorial (n + 1) → p ≤ (n + 1)):= by
    intro p hp n
    induction n with
    | zero =>
      -- Base case: if p divides 1!, then p ≤ 1
      simp
      intro hp
      linarith
    | succ n ih =>
      -- Inductive case: if p divides (n+2)!, then either p divides (n+2) or p divides (n+1)!
      intro h
      rw [Nat.factorial_succ] at h
      replace h : p ∣ n + 1 + 1 ∨ p ∣ (n + 1).factorial:= by exact (Nat.Prime.dvd_mul hp).mp h
      rcases h with h | h
      .
        -- Case 1: p divides (n+2)
        replace h : ∃ k : ℕ, n + 1 + 1 = p * k:= by exact h
        rcases h with ⟨k, hk⟩
        -- Show that k ≥ 1
        have hkpos : k ≥ 1:= by
          by_contra H
          simp at H
          subst k
          simp at hk
        -- Therefore p ≤ (n+2)
        have g1 : p * k ≥ p:= by exact Nat.le_mul_of_pos_right p hkpos
        linarith
      .
        -- Case 2: p divides (n+1)!
        replace ih:= ih h
        linarith

  -- Now we prove that the set of primes dividing 10! is exactly {2, 3, 5, 7}
  have h2 : {p : ℕ | p.Prime ∧ p ∣ Nat.factorial 10} = {2, 3, 5, 7}:= by
    ext p
    constructor
    .
      -- Forward direction: if p is prime and divides 10!, then p ∈ {2, 3, 5, 7}
      intro h
      simp at h
      rcases h with ⟨hp, h⟩
      specialize h1 p hp 9
      rw [show 9 + 1 = 10 by omega] at h1
      replace h1:= h1 h
      -- Prove that 4, 6, 8, 9, 10 are not prime
      have g1 : ¬(Nat.Prime 4):= by decide
      have g2 : ¬(Nat.Prime 6):= by decide
      have g3 : ¬(Nat.Prime 8):= by decide
      have g4 : ¬(Nat.Prime 9):= by decide
      have g5 : ¬(Nat.Prime 10):= by decide
      -- Since p is prime, p > 1
      have g6 : p > 1:= by exact Nat.Prime.one_lt hp
      -- Show that p is not equal to 4, 6, 8, 9, or 10
      replace g1 : p ≠ 4:= by
        by_contra H
        subst p
        trivial
      replace g2 : p ≠ 6:= by
        by_contra H
        subst p
        trivial
      replace g3 : p ≠ 8:= by
        by_contra H
        subst p
        trivial
      replace g4 : p ≠ 9:= by
        by_contra H
        subst p
        trivial
      replace g5 : p ≠ 10:= by
        by_contra H
        subst p
        trivial
      -- Therefore p must be 2, 3, 5, or 7
      simp
      omega
    .
      -- Backward direction: if p ∈ {2, 3, 5, 7}, then p is prime and divides 10!
      intro h
      simp
      simp at h
      rcases h with h | h | h | h
      all_goals
        subst p
        constructor
        .
          -- Prove that the number is prime
          decide
        .
          -- Prove that the number divides 10!
          repeat rw [Nat.factorial_succ]
          simp
          omega

  -- Finally, calculate the cardinality of the set {2, 3, 5, 7}
  rw [h2]
  rw [show ({2, 3, 5, 7} : Set ℕ) = ({2, 3, 5, 7} : Finset ℕ) by simp]
  rw [Set.ncard_coe_Finset]
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  all_goals
    simp
