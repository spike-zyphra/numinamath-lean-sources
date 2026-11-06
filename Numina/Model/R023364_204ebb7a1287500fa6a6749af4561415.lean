import Mathlib

theorem number_theory_104053 (n : ℕ) :
    8 * 3^(n + 2) * 25^(n + 1) < 7 * 5^(n + 2) * 15^(n + 1) ∧
    (8 * 3^(n + 2) * 25^(n + 1)) % 165 = (7 * 5^(n + 2) * 15^(n + 1)) % 165 := by
  have h1 : ∀ n : ℕ, 8 * 3 ^ (n + 2) * 25 ^ (n + 1) < 7 * 5 ^ (n + 2) * 15 ^ (n + 1) := by
    intro n 
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h2 : 8 * 3 ^ (n + 1 + 2) * 25 ^ (n + 1 + 1) < 7 * 5 ^ (n + 1 + 2) * 15 ^ (n + 1 + 1) := by
        have eq1 : 8 * 3 ^ (n + 1 + 2) * 25 ^ (n + 1 + 1) = 75 * (8 * 3 ^ (n + 2) * 25 ^ (n + 1)) := by
          ring_nf
        have eq2 : 7 * 5 ^ (n + 1 + 2) * 15 ^ (n + 1 + 1) = 75 * (7 * 5 ^ (n + 2) * 15 ^ (n + 1)) := by 
          ring_nf
        rw [eq1, eq2]
        have h20 : (8 * 3 ^ (n + 2) * 25 ^ (n + 1) : ℕ) < (7 * 5 ^ (n + 2) * 15 ^ (n + 1) : ℕ) := ih
        have h21 : 75 * (8 * 3 ^ (n + 2) * 25 ^ (n + 1) : ℕ) < 75 * (7 * 5 ^ (n + 2) * 15 ^ (n + 1) : ℕ) := by 
          omega
        exact_mod_cast h21
      exact h2
  have h5 : ∀ n : ℕ, (8 * 3 ^ (n + 2) * 25 ^ (n + 1)) % 165 = (7 * 5 ^ (n + 2) * 15 ^ (n + 1) ) % 165 := by
    intro n 
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have h7 : (8 * 3 ^ (n + 1 + 2) * 25 ^ (n + 1 + 1) ) =
          (8 * 3 ^ (n + 2) * 25 ^ (n + 1)) * (3 * 25) := by
        ring_nf
      have h8 : (7 * 5 ^ (n + 1 + 2) * 15 ^ (n + 1 + 1) ) =
          (7 * 5 ^ (n + 2) * 15 ^ (n + 1) ) * (5 * 15) := by
        ring_nf
      rw [h7, h8]
      simp [Nat.mul_mod, ih]
      <;> try { omega }
  constructor
  · -- Proof of the inequality.
    exact h1 n
  · -- Proof of the congruence.
    exact h5 n