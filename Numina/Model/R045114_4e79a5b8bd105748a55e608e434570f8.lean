import Mathlib

theorem algebra_215752 {a : ℕ → ℝ} (ha1 : a 1 = 2)
    (han : ∀ n > 0, a (n + 1) = (2 * a n - 4) / (a n + 6)) :
    ∀ n > 0, a n = (4 - 2 * n) / n := by 
  intro n hn 
  induction n with 
  | zero => 
    exfalso 
    linarith
  | succ n ih =>
    cases n with 
    | zero =>
      rw [ha1]
      norm_num
    | succ n =>
      have h2 := ih (by linarith)
      have eq1 : a (n + 1 + 1) = (2 * a (n + 1) - 4) / (a (n + 1) + 6) := by 
        specialize han (n + 1) (by linarith)
        simpa using han 
      rw [eq1]
      simp [h2] at *
      field_simp [(show (n + 1 : ℝ) ≠ 0 by positivity), (show (n + 2 : ℝ) ≠ 0 by positivity)]
      <;> ring_nf <;> field_simp [(show (n + 1 : ℝ) ≠ 0 by positivity), (show (n + 2 : ℝ) ≠ 0 by positivity)]
      <;> ring