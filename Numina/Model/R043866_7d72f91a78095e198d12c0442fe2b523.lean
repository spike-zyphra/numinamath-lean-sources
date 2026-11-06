import Mathlib

theorem algebra_280960 (a : ℕ → ℝ) (ha1 : a 1 = 0)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 4 * Real.sqrt (a n + 1) + 4) :
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
      have h1 : a (n + 1 + 1) = a (n + 1) + 4 * Real.sqrt (a (n + 1) + 1) + 4 := by
        specialize han (n + 1) (by linarith)
        simpa using han
      have h2 : n + 1 ≥ 1 := by linarith
      have h3 : a (n + 1) = 4 * (n + 1) ^ 2 - 4 * (n + 1) := by
        specialize ih (by linarith)
        simpa using ih
      rw [show n + 1 + 1 = n + 2 by omega]
      rw [h1, h3]
      have h4 : Real.sqrt (4 * (↑n + 1) ^ 2 - 4 * (↑n + 1) + 1) = 2 * (↑n + 1) - 1 := by
        have h5 : (4 * (↑n + 1 : ℝ) ^ 2 - 4 * (↑n + 1) + 1) = (2 * (↑n + 1) - 1) ^ 2 := by
          ring
        rw [h5]
        have h6 : 0 ≤ (2 * (↑n + 1) - 1 : ℝ) := by
          have h7 : (↑n : ℝ) ≥ 0 := by exact_mod_cast (show (n : ℕ) ≥ 0 by omega)
          nlinarith
        rw [Real.sqrt_sq (show 0 ≤ (2 * (↑n + 1) - 1 : ℝ) by linarith)]
      field_simp [h4]
      ring