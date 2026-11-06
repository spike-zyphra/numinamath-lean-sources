import Mathlib

theorem algebra_134237 {s : ℕ → ℝ} (r : ℝ) (hr : r ≠ 0)
    (h₀ : ∀ n, s (n + 1) = s n * r) :
    ∀ n, s n = s 0 * r ^ n := by
  intro n
  induction n with
  | zero =>
    -- Base case: n = 0
    -- We need to prove s 0 = s 0 * r ^ 0
    -- Since r ^ 0 = 1, this simplifies to s 0 = s 0 * 1, which is trivial.
    simp 
  | succ k ih =>
    -- Inductive step: Assume it holds for k, prove it for k + 1
    -- We need to prove s (k + 1) = s 0 * r ^ (k + 1)
    have h₁ : s (k + 1) = s k * r := h₀ k 
    rw [h₁]
    -- Now we have s k * r = s 0 * r ^ (k + 1)
    -- The induction hypothesis is s k = s 0 * r ^ k
    -- Substitute this into the left side
    rw [ih]
    -- Simplify: (s 0 * r ^ k) * r = s 0 * r ^ (k + 1)
    ring_nf