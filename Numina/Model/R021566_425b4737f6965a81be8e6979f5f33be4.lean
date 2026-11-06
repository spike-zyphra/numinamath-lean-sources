import Mathlib

theorem algebra_302207 {a : ℕ → ℝ} (ha1 : a 1 = 0)
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
      have h1 := ih (by linarith)
      have h2 := han (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at h2
      rw [h2]
      rw [h1]
      have h3 : Real.sqrt (4 * (n + 1 : ℝ) ^ 2 - 4 * (n + 1 : ℝ) + 1) = 2 * (n + 1 : ℝ) - 1 := by 
        have h4 : (4 * (n + 1 : ℝ) ^ 2 - 4 * (n + 1 : ℝ) + 1) = (2 * (n + 1 : ℝ) - 1) ^ 2 := by ring
        rw [h4]
        have h5 : 2 * (n + 1 : ℝ) - 1 ≥ 0 := by 
          nlinarith 
        rw [Real.sqrt_sq (h5)]
      have h7 : Real.sqrt ((4 * (n + 1 : ℝ) ^ 2 - 4 * (n + 1 : ℝ)) + 1) = 2 * (n + 1 : ℝ) - 1 := by 
        have h11 : (4 * (n + 1 : ℝ) ^ 2 - 4 * (n + 1 : ℝ) ) + 1 = 4 * (n + 1 : ℝ) ^ 2 - 4 * (n + 1 : ℝ) + 1 := by ring
        rw [h11]
        exact h3
      simp [h7]
      ring_nf