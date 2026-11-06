import Mathlib

theorem algebra_159526 {a : ℕ → ℝ} (ha0 : a 0 = 2) (han : ∀ n ≥ 1, a n = (n + 2) * a (n - 1)) :
    ∀ n, a n = Nat.factorial (n + 2) := by
  intro n
  have h1 : ∀ n : ℕ, a n = (Nat.factorial (n + 2) : ℝ) := by
    intro n 
    induction n with
    | zero =>
      rw [ha0]
      norm_num [Nat.factorial]
    | succ k ih =>
      have eq2 : a (k + 1) = (k + 1 + 2) * a k := by
        specialize han (k + 1) (by linarith)
        simp [show k + 1 - 1 = k by omega] at han ⊢
        <;> linarith
      rw [eq2]
      rw [ih]
      simp [Nat.factorial]
      <;> ring_nf <;> norm_num
  specialize h1 n
  simpa using h1