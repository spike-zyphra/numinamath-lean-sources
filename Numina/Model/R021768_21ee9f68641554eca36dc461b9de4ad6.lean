import Mathlib

def triangular_number (n : ℕ) : ℕ := n * (n + 1) / 2

theorem algebra_134252 {t : ℕ → ℕ} (ht0 : t 0 = 0) (h tk : ∀ k, t (k + 1) = t k + k + 1) :
    ∀ n, t n = triangular_number n := by 
  intro n
  induction n with 
  | zero => 
    simp [ht0, triangular_number]
  | succ k ih => 
    have hk1 : t (k + 1) = t k + k + 1 := by
      specialize tk k
      simpa using tk 
    rw [hk1]
    rw [ih]
    simp [triangular_number]
    <;> ring_nf <;> omega