import Mathlib

theorem number_theory_289880 :
  (∀ n : ℕ, Even n → ¬∃ m : ℕ, n^2 + 1 = 3 * m^2) ∧
  (∀ n : ℕ, ¬∃ m : ℕ, n^2 + 1 = 7 * m^2) := by
  constructor
  · -- Proof of the first statement
    intro n hn
    rintro ⟨m, hm⟩
    rcases hn with ⟨k, hk⟩
    rw [show n = 2 * k by omega] at hm
    have h1 : (2 * k) ^ 2 + 1 = 3 * m ^ 2 := by linarith
    have h6 : (k) ^ 2 % 3 = 0 ∨ (k) ^ 2 % 3 = 1 := by
      have h1' : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by
        omega
      rcases h1' with (h1' | h1' | h1')
      · -- k % 3 = 0
        simp [h1', pow_two, Nat.mul_mod, Nat.add_mod]
      · -- k % 3 = 1
        simp [h1', pow_two, Nat.mul_mod, Nat.add_mod]
      · -- k % 3 = 2
        simp [h1', pow_two, Nat.mul_mod, Nat.add_mod]
    -- Now, derive that k^2 % 3 = 2 from the equation
    have h7 : (k ^ 2) % 3 = 2 := by
      have eq1 : (2 * k) ^ 2 + 1 = 3 * m ^ 2 := h1
      have h8 : ((2 * k) ^ 2 + 1) % 3 = (3 * m ^ 2) % 3 := by 
        omega
      have h9 : ((2 * k) ^ 2 + 1) % 3 = (k ^ 2 + 1) % 3 := by
        ring_nf
        <;> omega
      have h10 : (3 * m ^ 2) % 3 = 0 := by 
        omega
      have h11 : (k ^ 2 + 1) % 3 = 0 := by 
        omega
      omega 
    omega
  · -- Proof of the second statement
    intro n
    rintro ⟨m, hm⟩
    have h5 : n ^ 2 % 7 = 0 ∨ n ^ 2 % 7 = 1 ∨ n ^ 2 % 7 = 2 ∨ n ^ 2 % 7 = 4 := by 
      have h5' : n % 7 = 0 ∨ n % 7 = 1 ∨ n % 7 = 2 ∨ n % 7 = 3 ∨ n % 7 = 4 ∨ n % 7 = 5 ∨ n % 7 = 6 := by
        omega 
      rcases h5' with (h5' | h5' | h5' | h5' | h5' | h5' | h5')
      all_goals 
        simp [h5', pow_two, Nat.mul_mod, Nat.add_mod]
    -- Now, from `hm`, derive congruence modulo 7
    have h8 : (n^2 + 1) % 7 = 0 := by 
      omega
    -- From such substitution. Now we have from `n^2 \pmod 7:`.
    -- `n^2 + 1 \equiv 0 (mod 7) \implies n^2 \equiv -1 \equiv 6 (mod 7)`.
    have h9 : n ^ 2 % 7 = 6 := by 
      omega 
    omega