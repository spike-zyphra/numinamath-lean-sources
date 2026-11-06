import Mathlib

theorem number_theory_292677 {A B : ℤ} {k n : ℕ} (hA : A % 10^k = B % 10^k) :
    (A^n) % 10^k = (B^n) % 10^k := by
  have h2 : ∀ n : ℕ, (A ^ n) % 10^k = (B ^ n) % 10^k := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      have h3 : (A ^ (n + 1)) % 10^k = (B ^ (n + 1)) % 10^k := by
        have h4 : (A ^ (n + 1) : ℤ) = A * (A ^ n) := by ring
        have h5 : (B ^ (n + 1) : ℤ) = B * (B ^ n) := by ring
        rw [h4, h5]
        have h6 : A % 10^k = B % 10^k := hA
        have h7 : (A ^ n) % 10^k = (B ^ n) % 10^k := ih
        simp [Int.mul_emod, h6, h7]
      exact h3
  specialize h2 n
  exact h2