import Mathlib

theorem number_theory_112334 (n : ℕ) :
    133 ∣ (11 ^ (n + 2) + 12 ^ (2 * n + 1)) := by
  induction n with
  | zero =>
    use 1
    simp
  | succ n ih =>
    have h1 : 11 ^ (n + 2 + 1) + 12 ^ (2 * (n + 1) + 1) = 11 * (11 ^ (n + 2)) + 144 * (12 ^ (2 * n + 1)) := by
      ring_nf
    rw [h1]
    omega