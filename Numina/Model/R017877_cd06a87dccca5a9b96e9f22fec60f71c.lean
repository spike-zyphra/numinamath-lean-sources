import Mathlib

theorem algebra_327836 {a : ℕ → ℤ} (ha1 : a 1 = 2) (han : ∀ n > 0, a (n + 1) = 4 * a n - 3 * n + 1) :
    ∀ n > 0, a n = 4 ^ (n - 1) + n := by
  intro n hn
  induction n with
  | zero => 
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      rw [ha1]
      simp
    | succ n => 
      have h1 : a (n + 1) = 4 ^ (n) + (n + 1 : ℕ) := by
        specialize ih (by linarith)
        simpa using ih
      have h2 : a ((n + 1) + 1) = 4 * a (n + 1) - 3 * ((n + 1 : ℕ) ) + 1 := by 
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [h2]
      rw [h1]
      simp [pow_succ, pow_zero, mul_add, add_mul]
      <;> ring_nf <;> omega