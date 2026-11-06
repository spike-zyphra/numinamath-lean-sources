import Mathlib

theorem algebra_130512 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (x : ℕ → ℝ) (hx0 : x 0 = 0)
    (hxn : ∀ n, x (n + 1) = x n + a + Real.sqrt (b ^ 2 + 4 * a * x n)) :
    ∀ n, x n = a * n ^ 2 + b * n := by 
  intro n
  induction n with
  | zero =>
    simp [hx0]
  | succ n ih =>
    have h1 : x (n + 1) = x n + a + Real.sqrt (b ^ 2 + 4 * a * x n) := hxn n
    rw [h1]
    rw [ih]
    have h2 : b ^ 2 + 4 * a * (a * n ^ 2 + b * n) = (2 * a * n + b) ^ 2 := by
      ring_nf
    have h3 : Real.sqrt (b ^ 2 + 4 * a * (a * n ^ 2 + b * n)) = (2 * a * n + b) := by
      rw [h2]
      have h4 : (2 * a * n + b) ≥ 0 := by
        positivity
      rw [Real.sqrt_sq (by linarith [h4])]
    simp [h3]
    ring_nf
    <;> simp [add_assoc] <;> ring