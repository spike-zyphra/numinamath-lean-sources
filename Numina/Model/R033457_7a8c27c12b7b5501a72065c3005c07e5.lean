import Mathlib

theorem algebra_271127 {a : ℕ → ℝ} (ha1 : a 1 = 0)
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
      have h1 : a (n + 1) = ((n + 1 : ℝ) ) ^ 2 - 1 := by
        specialize ih (by linarith)
        simpa using ih
      have h2 := han (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at h2
      rw [h2]
      rw [h1]
      have h3 : 1 + (( (n + 1 : ℝ) ) ^ 2 - 1 ) = ( (n + 1 : ℝ) ) ^ 2 := by
        ring
      have h4 : Real.sqrt (1 + ( ( (n + 1 : ℝ) ) ^ 2 - 1 ) ) = (n + 1 : ℝ) := by
        rw [h3]
        have h5 : Real.sqrt ( ( (n + 1 : ℝ) ) ^ 2 ) = (n + 1 : ℝ) := by
          rw [Real.sqrt_sq (by
            have : (n : ℝ) ≥ 0 := by 
              exact_mod_cast (show (n) ≥ (0: ℕ) by omega)
            have : (n + 1 : ℝ) ≥ 0 := by linarith
            linarith
          )
          ]
        exact h5
      rw [h4]
      field_simp
      <;> ring