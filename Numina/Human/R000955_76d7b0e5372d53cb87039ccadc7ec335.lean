import Mathlib

/- Consider the geometric sequence $\frac{16}{9}, \frac{8}{3}, 4, 6, 9, \ldots$. What is the eighth term of the sequence? Express your answer as a common fraction. -/
theorem algebra_19362 (a : ℕ → ℝ) (ha0 : a 0 = 16 / 9) (ha1 : a 1 = 8 / 3) (h : ∀ n, a (n + 1) = a n * a 1 / a 0) : a 7 = 243 / 8 := by
  -- The formula for the nth term of a geometric sequence
  -- a_n = a_0 * r^n = 16 / 9 * (3 / 2)^n
  have H (n : ℕ) : a n = 16 / 9 * (3 / 2) ^ n := by
    -- Proof by induction
    induction n with
    | zero => simp [ha0]
    | succ n ih =>
        rw [h, ha0, ha1, pow_succ]
        linarith only [ih]
  -- The eighth term is a_7 = 16 / 9 * (3 / 2)^7 = 243 / 8
  rw [H]
  norm_num
