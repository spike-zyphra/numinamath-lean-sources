import Mathlib

theorem algebra_260823 (a : ℕ → ℤ) (ha1 : a 1 = 2) (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * n) :
    a 100 = 9902 := by
  have h1 : ∀ n : ℕ, a (n + 1) = 2 + n * (n + 1) := by
    intro n
    induction n with
    | zero =>
      simp [ha1]
      <;> ring
    | succ n ih =>
      calc
        a ((n + 1) + 1)
          = a (n + 1) + 2 * (n + 1) := han (n + 1) (by linarith)
        _ = (2 + n * (n + 1)) + 2 * (n + 1) := by rw [ih]
        _ = 2 + (n + 1) * ((n : ℤ) + 2) := by ring
      <;> ring
  have h100 := h1 99
  norm_num at h100 ⊢
  exact h100