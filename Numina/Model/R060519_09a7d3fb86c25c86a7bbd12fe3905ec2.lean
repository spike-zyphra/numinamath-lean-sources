import Mathlib

theorem number_theory_215495 (n : ℕ) :
    10 ∣ 2^(2^(n+2)) + 4 := by
  have h1 : ∀ n : ℕ, 2^(2^(n + 2)) % 10 = 6 := by
    intro n
    induction n with
    | zero => 
      norm_num
    | succ k ih =>
      have h2 : 2^(2^((k + 1 + 2))) = (2^(2^(k + 2))) ^ 2 := by
        ring_nf
        <;> simp [pow_mul, pow_two]
        <;> ring_nf
      rw [h2] at *
      have h3 : (2 ^ (2 ^ (k + 2)) : ℕ) % 10 = 6 := ih
      have h4 : ((2 ^ (2 ^ (k + 2)) : ℕ) ^ 2) % 10 = 6 := by
        simp [Nat.pow_mod, h3]
      exact h4
  have h2 := h1 n
  omega