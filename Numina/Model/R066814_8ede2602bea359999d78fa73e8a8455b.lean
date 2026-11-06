import Mathlib

theorem algebra_319744 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (x : ℕ → ℝ) (hx0 : x 0 = 0) (hxn : ∀ n, x (n + 1) = x n + a + Real.sqrt (b ^ 2 + 4 * a * x n)) :
    ∀ n, x n = a * n ^ 2 + b * n := by
  intro n
  induction n with
  | zero =>
    simp [hx0]
  | succ n ih =>
    have eq1 : x (n + 1) = x n + a + Real.sqrt (b ^ 2 + 4 * a * x n) := by
      specialize hxn n
      simpa using hxn
    rw [eq1]
    rw [ih]
    have h : (b ^ 2 + 4 * a * (a * n ^ 2 + b * n)) = (b + 2 * a * n) ^ 2 := by
      ring
    have h2 : Real.sqrt ((b ^ 2 + 4 * a * (a * n ^ 2 + b * n))) = b + 2 * a * n := by
      rw [show b ^ 2 + 4 * a * (a * n ^ 2 + b * n) = (b + 2 * a * n) ^ 2 by linarith [h]]
      have h3 : 0 ≤ b + 2 * a * n := by
        positivity
      rw [Real.sqrt_sq (show (b + 2 * a * n) ≥ 0 by linarith)]
    rw [h2]
    simp [sq]
    <;> ring