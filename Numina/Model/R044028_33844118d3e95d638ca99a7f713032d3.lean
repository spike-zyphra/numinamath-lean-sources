import Mathlib

theorem number_theory_301927 (n : ℕ) (h₀ : n > 0) :
    (Nat.digits 10 (n * (n - 1))).sum ≠ (Nat.digits 10 ((n + 1) ^ 2)).sum := by 
  intro h 
  have h1 : (n * (n - 1)) % 9 = ((Nat.digits 10 (n * (n - 1))).sum) % 9 := by 
    rw [Nat.modEq_nine_digits_sum (n * (n - 1))]
  have h2 : ((n + 1) ^ 2) % 9 = ((Nat.digits 10 ((n + 1) ^ 2)).sum) % 9 := by 
    rw [Nat.modEq_nine_digits_sum ((n + 1) ^ 2)]
  -- Derive that the expressions for A and B must be congruent
  have h3 : (n * (n - 1)) % 9 = ((n + 1) ^ 2) % 9 := by 
    omega 
  -- From congruence, derive that (3 * n + 1) % 9 = 0. This is impossible.
  have h8 : (3 * n + 1) % 9 = 0 := by 
    -- From h3 : (n * (n - 1)) % 9 = ((n + 1) ^ 2) % 9.
    -- Therefore (n + 1) ^ 2 ≡ n * (n - 1) \pmod 9
    -- Expanding: n^2 + 2n + 1 ≡ n^2 - n \pmod 9
    -- Simplify: 3n + 1 ≡ 0 \pmod 9
    have h5 : (n * (n - 1)) % 9 = ((n + 1) ^ 2) % 9 := h3 
    cases n with 
    | zero => 
      exfalso; linarith 
    | succ n => 
      cases n with 
      | zero => 
        simp at h5 ⊢ 
        all_goals omega 
      | succ n => 
        simp [Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.mul_assoc, Nat.pow_two] at h5 ⊢ 
        all_goals omega 
  -- The congruence (3 * n + 1) % 9 = 0 is impossible. Show contradiction.
  have h9 : (3 * n + 1) % 9 ≠ 0 := by 
    omega 
  -- Derive contradiction
  contradiction