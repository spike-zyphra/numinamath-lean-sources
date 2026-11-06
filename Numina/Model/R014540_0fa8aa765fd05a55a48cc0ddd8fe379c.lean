import Mathlib

theorem algebra_210679 {a : ℕ → ℝ} (ha1 : a 1 = 0) (han : ∀ n ≥ 1, a (n + 1) = a n + 4 * Real.sqrt (a n + 1) + 4) :
    ∀ n ≥ 1, a n = 4 * n ^ 2 - 4 * n := by
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
      have h1 := ih (by linarith)
      have eq1 : a ((n + 1) + 1) = a (n + 1) + 4 * Real.sqrt (a (n + 1) + 1) + 4 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      rw [eq1]
      rw [h1]
      have h2 : Real.sqrt (4 * ((n + 1 : ℝ) ^ 2) - 4 * ((n + 1 : ℝ)) + 1) = (2 * (n : ℝ) + 1) := by
        have h3 : (4 * ((n + 1 : ℝ) ^ 2) - 4 * ((n + 1 : ℝ)) + 1) = (2 * (n : ℝ) + 1) ^ 2 := by
          ring_nf
        rw [h3]
        have h4 : 0 ≤ (2 * (n : ℝ) + 1) := by
          have hn1 : (n : ℝ) ≥ (0 : ℝ) := by exact_mod_cast (show (n : ℕ) ≥ 0 by omega)
          linarith
        rw [Real.sqrt_sq (h4)]
      field_simp [h2]
      ring_nf
      <;> norm_num
      <;> ring