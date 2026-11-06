import Mathlib

theorem algebra_251096 {x : ℕ → ℝ} (hx1 : x 1 = 4)
    (hxn : ∀ n ≥ 2, x n = ((5 * n + 2) / (5 * n - 3 : ℝ) * x (n - 1) + 7 * (5 * n + 2))) :
    ∀ n ≥ 1, x n = (49 * n - 45) * (5 * n + 2) / 7 := by 
  intro n hn
  induction n with 
  | zero => 
    exfalso 
    linarith
  | succ n ih =>
    cases n with
    | zero => 
      rw [hx1]
      norm_num
    | succ n => 
      have h1 := ih (by linarith)
      have h2 := hxn (n + 2) (by linarith)
      simp [show n + 2 - 1 = n + 1 by omega] at h2 
      rw [h2, h1]
      field_simp [(show (5 * ((n : ℝ) + 2) - 3 : ℝ) ≠ 0 by
        by_contra h 
        have : (n : ℝ) = -1 / 5 := by 
          nlinarith 
        nlinarith [show (n : ℝ) ≥ 0 by simp]
      ) ]
      ring_nf
      <;> 
      field_simp <;> 
      ring