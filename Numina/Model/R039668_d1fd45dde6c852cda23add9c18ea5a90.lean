import Mathlib

theorem algebra_10639 {a : ℕ → ℝ} (ha1 : a 1 = 0)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 1 + 2 * Real.sqrt (1 + a n)) :
    ∀ n ≥ 1, a n = n ^ 2 - 1 := by
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
      have h3 : a (n + 1 + 1) = a (n + 1) + 1 + 2 * Real.sqrt (1 + a (n + 1)) := by
        specialize han (n + 1) (by linarith)
        simpa using han
      have h4 : n + 1 ≥ 1 := by linarith
      have h5 : a (n + 1) = (n + 1 : ℕ) ^ 2 - 1 := by 
        specialize ih (by linarith)
        simpa using ih
      rw [h3]
      rw [h5]
      have h6 : Real.sqrt (1 + ((↑n + 1 : ℝ) ^ 2 - 1 : ℝ)) = (↑n + 1 : ℝ) := by
        have h1 : (1 + ((↑n + 1 : ℝ) ^ 2 - 1 : ℝ)) = (↑n + 1 : ℝ) ^ 2 := by
          ring
        rw [h1]
        have h2 : Real.sqrt ((↑n + 1 : ℝ) ^ 2 ) = (↑n + 1 : ℝ) := by
          rw [Real.sqrt_sq]
          positivity
        rw [h2]
      simp [h6]
      field_simp at *
      <;> ring