import Mathlib

theorem number_theory_119474 {A B : ℤ} {k n : ℕ} (hA : A % 10 ^ k = B % 10 ^ k) :
    (A ^ n) % 10 ^ k = (B ^ n) % 10 ^ k := by 
  have h2 : ∀ n : ℕ, (A ^ n) % 10 ^ k = (B ^ n) % 10 ^ k := by
    intro n
    induction n with
    | zero =>
      simp 
    | succ n ih =>
      have h3 : (A ^ (n + 1)) % 10 ^ k = (A ^ n * A) % 10 ^ k := by ring
      have h4 : (B ^ (n + 1)) % 10 ^ k = (B ^ n * B) % 10 ^ k := by ring
      rw [h3, h4]
      simp [Int.mul_emod, ih, hA]
  exact h2 n