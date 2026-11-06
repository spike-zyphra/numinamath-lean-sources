import Mathlib

theorem number_theory_257631 (p q : ℕ) (hp : p.Prime) (hq : q.Prime)
    (h : p > 0 ∧ q > 0) (h1 : p^2 - q^3 = 1) :
    (p = 3 ∧ q = 2) := by
  have h2 : p^2 = q^3 + 1 := by
    omega
  by_cases h4 : q % 2 = 1
  · -- Assume q is odd, so q % 2 = 1.
    have h5 : p % 2 = 0 := by
      have h6 : q % 2 = 1 := h4
      have h7 : q ^ 3 % 2 = 1 := by
        simp [Nat.pow_mod, h6]
      have h8 : p ^ 2 % 2 = 0 := by
        omega
      have h9 : p % 2 = 0 := by
        by_contra h
        push_neg at h
        have h10 : p % 2 = 1 := by
          omega
        have h11 : (p ^ 2) % 2 = 1 := by
          simp [Nat.pow_mod, h10]
        omega
      assumption
    have h8 : p = 2 := by
      by_cases h9 : p > 2
      · -- If p > 2, it's not prime. Contradiction.
        have h10 : ¬p.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ p by omega) (by omega) (by omega)
        contradiction
      · -- So p ≤ 2.
        have h11 : p ≤ 2 := by linarith
        interval_cases p <;> norm_num at hp ⊢ <;> try { contradiction } <;> try { tauto }
    -- Now substituting p = 2 in equation, which gives q ^ 3 = 3, contradiction.
    rw [h8] at h2
    -- Equation becomes 2^2 = q^3 + 1 ⇒ 4 = q^3 + 1 ⇒ q^3 = 3.
    have h9 : q ^ 3 = 3 := by
      nlinarith
    -- Show contradiction.
    have h10 : q ≤ 2 := by
      by_contra h11
      push_neg at h11
      have h15 : q ^ 3 ≥ 8 := by
        have h16 : q ≥ 2 := by linarith
        have h12 : q ^ 3 ≥ (2 : ℕ) ^ 3 := by
          apply Nat.pow_le_pow_of_le_left
          all_goals linarith
        norm_num at h12 ⊢
        nlinarith
      omega
    -- Now try possible values.
    interval_cases q <;> norm_num at hq h9 h10 ⊢ <;> try { contradiction } <;> try { tauto }
  · -- Assume q is even, so q % 2 = 0.
    have h9 : q % 2 = 0 := by
      omega
    have h10 : q = 2 := by
      by_cases h11 : q > 2
      · -- If q > 2, it's not prime. Contradiction.
        have h12 : ¬q.Prime := by
          apply Nat.not_prime_of_dvd_of_lt (show 2 ∣ q by omega) (by omega) (by omega)
        contradiction
      · -- So q ≤ 2.
        have h13 : q ≤ 2 := by linarith
        interval_cases q <;> norm_num at hq ⊢ <;> try { contradiction } <;> try { tauto }
    -- Now substituting q = 2 in equation, which gives p ^ 2 = 9, so p = 3.
    have h11 : p ^ 2 = 9 := by
      rw [h10] at h2
      nlinarith
    have hp3 : p = 3 := by
      nlinarith
    constructor
    · -- p = 3
      exact hp3
    · -- q = 2
      exact h10