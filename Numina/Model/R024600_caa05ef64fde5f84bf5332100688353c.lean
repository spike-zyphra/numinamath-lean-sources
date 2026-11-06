import Mathlib


lemma lemma_1 (n : ℕ) : 5^(n + 5) * 3^(n + 2) + 5^(n + 2) * 3^(n + 4) + 3 * 15^(n + 1) =
    15 * (5^(n + 4) * 3^(n + 1) + 5^(n + 1) * 3^(n + 3) + 3 * 15^n) := by
  have h1 : 5 ^ (n + 5) * 3 ^ (n + 2) + 5 ^ (n + 2) * 3 ^ (n + 4) + 3 * 15 ^ (n + 1) =
        15 * (5 ^ (n + 4) * 3 ^ (n + 1) + 5 ^ (n + 1) * 3 ^ (n + 3) + 3 * 15 ^ n) := by
    rw [pow_add, pow_add, pow_add, pow_add, pow_add, pow_add]
    ring_nf
  exact h1


theorem number_theory_115570 (n : ℕ) :
    (5^(n+4) * 3^(n+1) + 5^(n+1) * 3^(n+3) + 3 * 15^n) % 2013 = 0 := by

  have h1 : ∀ n : ℕ, (5 ^ (n + 4) * 3 ^ (n + 1) + 5 ^ (n + 1) * 3 ^ (n + 3) + 3 * 15 ^ n) % 2013 = 0 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : (5 ^ ((n + 1 + 4)) * 3 ^ ((n + 1 + 1)) + 5 ^ ((n + 1 + 1)) * 3 ^ ((n + 1 + 3)) + 3 * 15 ^ (n + 1)) =
          15 * (5 ^ (n + 4) * 3 ^ (n + 1) + 5 ^ (n + 1) * 3 ^ (n + 3) + 3 * 15 ^ n) := by
        ring_nf
      rw [h2]
      have h15 : (15 * (5 ^ (n + 4) * 3 ^ (n + 1) + 5 ^ (n + 1) * 3 ^ (n + 3) + 3 * 15 ^ n)) % 2013 = 0 := by
        have h16 : (5 ^ (n + 4) * 3 ^ (n + 1) + 5 ^ (n + 1) * 3 ^ (n + 3) + 3 * 15 ^ n) % 2013 = 0 := ih
        simp [Nat.mul_mod, h16]
      exact h15
  exact h1 n