import Mathlib

def fib (n : ℕ) : ℕ := match n with
| 0 => 0
| 1 => 1
| n + 2 => fib (n + 1) + fib n

theorem number_theory_270601 : ∀ n, 5 ∣ fib (5 * n) := by
  intro n 
  induction n with
  | zero =>
    simp [fib]
  | succ k ih =>
    have h1 : fib (5 * (k + 1)) = 5 * (fib (5 * k + 1)) + 3 * (fib (5 * k)) := by 
      simp [show 5 * (k + 1) = 5 * k + 5 by ring]
      <;> simp [fib]
      <;> ring_nf <;> try omega
      all_goals 
        ring_nf 
        <;> omega 
    rw [h1]
    omega