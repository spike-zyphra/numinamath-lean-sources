import Mathlib

theorem algebra_310654 (x : ℝ) (hx : 7 ≤ x) : Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5 ↔ x = 11 := by
  constructor
  · -- If $\sqrt{x-2} + \sqrt{x-7} = 5$, then $x = 11$.
    intro h
    have h1 : Real.sqrt (x - 2) ≥ 0 := by apply Real.sqrt_nonneg
    have h2 : Real.sqrt (x - 7) ≥ 0 := by apply Real.sqrt_nonneg

    have h3 : Real.sqrt (x - 2) = 3 := by 
      have h_eq : Real.sqrt (x - 2) = 3 := by
        have h4 : Real.sqrt (x - 2) + Real.sqrt (x - 7) = 5 := h
        have h5 : Real.sqrt (x - 2) ≥ 0 := by apply Real.sqrt_nonneg
        have h6 : Real.sqrt (x - 7) ≥ 0 := by apply Real.sqrt_nonneg
        nlinarith [Real.sq_sqrt (show 0 ≤ x - 2 by linarith), Real.sq_sqrt (show 0 ≤ x - 7 by linarith), sq_nonneg (Real.sqrt (x - 2) - Real.sqrt (x - 7))]
      exact h_eq

    have hx_eq : x = 11 := by
      have h_eq : Real.sqrt (x - 2) = 3 := by
        exact h3
      have h7 : x - 2 = 9 := by
        calc
          x - 2 = (Real.sqrt (x - 2)) ^ 2 := by rw [Real.sq_sqrt]; linarith
          _ = 3 ^ 2 := by rw [h_eq]
          _ = 9 := by norm_num
      linarith
    exact hx_eq
  · -- If $x = 11$, then $\sqrt{x-2} + \sqrt{x-7} = 5$.
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt (11 - 2) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (11 - 7) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    linarith