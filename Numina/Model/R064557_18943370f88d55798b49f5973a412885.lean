import Mathlib

theorem algebra_209385 {x : ℕ → ℤ} (hx1 : x 1 = 1) (hxn : ∀ n ≥ 1, x (n + 1) = x n + 2 * n + 1) :
    x 2018 = 2018 ^ 2 := by
  have h : ∀ n, x (n + 1) = ((n + 1 : ℕ) : ℤ) ^ 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
      exact hx1
    | succ n ih =>
      have h1 : (n + 1 : ℕ) ≥ 1 := by
        induction n with
        | zero => norm_num
        | succ n ih => omega
      have h2 := hxn (n + 1) h1
      simp [show x (n + 1 + 1) = x (n + 1) + 2 * (n + 1) + 1 by exact h2] at *
      simp [ih] at *
      <;> ring_nf <;> simp [sq] <;> ring
  specialize h 2017
  norm_num at h ⊢
  exact h