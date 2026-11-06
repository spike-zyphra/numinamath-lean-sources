import Mathlib

/-
Let $x_1=97$, and for $n>1$, let $x_n=\frac{n}{x_{n-1}}$. Calculate the product $x_1x_2x_3x_4x_5x_6x_7x_8$.
-/

-- Offset from `ℕ+` to `ℕ`
theorem algebra_94698
  (x : ℕ → ℝ)
  (hx1 : x 0 = 97)
  (hxn : ∀ n > 0, x n = (n + 1) / x (n - 1))
  : x 0 * x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * x 7 = 384
:= by
  -- We can only divide if the denominator is never `0`, so we prove it by induction
  have hx_pos : ∀ i : ℕ, x i ≠ 0 := by
    intro i
    induction' i with i ih
    . linarith
    rw [hxn]
    simp
    constructor
    any_goals linarith
    exact ih
  -- Rearrange to a form without division
  have hxn : ∀ n > 0, x (n - 1) * x n  = n + 1 := by
    intro n hn
    rw [mul_comm, hxn n hn, div_mul, div_self] <;> simp [hx_pos]
  -- We can now apply the form iteratively to every pair of terms
  calc
    x 0 * x 1 * x 2 * x 3 * x 4 * x 5 * x 6 * x 7 = (x 0 * x 1) * (x 2 * x 3) * (x 4 * x 5) * (x 6 * x 7) := by ring
    _ = 2 * 4 * 6 * 8 := by
      rw [hxn 1 (by linarith), hxn 3 (by linarith), hxn 5 (by linarith), hxn 7 (by linarith)]
      ring
    _ = 384 := by norm_num