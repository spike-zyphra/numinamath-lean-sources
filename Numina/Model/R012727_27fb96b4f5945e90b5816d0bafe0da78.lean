import Mathlib

theorem algebra_165763 (x : ℝ) (hx : x ≥ 0) :
    Real.sqrt (x + 8 + 2 * Real.sqrt (x + 7)) +
    Real.sqrt (x + 1 - Real.sqrt (x + 7)) = 4 ↔ x = 2 := by
  constructor
  · -- Forward implication: if the equation satisfies, then x=2.
    intro h_eq
    have h1 : 0 ≤ x + 7 := by linarith
    have h17 : Real.sqrt (x + 8 + 2 * Real.sqrt (x + 7)) = Real.sqrt (x + 7) + 1 := by
      have h4 : x + 8 + 2 * Real.sqrt (x + 7) = (Real.sqrt (x + 7) + 1) ^ 2 := by
        nlinarith [Real.sqrt_nonneg (x + 7), Real.sq_sqrt (show 0 ≤ (x + 7 : ℝ) by linarith)]
      rw [h4]
      have h5 : Real.sqrt ((Real.sqrt (x + 7) + 1) ^ 2) = Real.sqrt (x + 7) + 1 := by 
        rw [Real.sqrt_sq]
        linarith [Real.sqrt_nonneg (x + 7)]
      rw [h5]
      all_goals linarith
    have h_eq3 : (Real.sqrt (x + 7) + 1) + Real.sqrt (x + 1 - Real.sqrt (x + 7)) = 4 := by
      have h33 : Real.sqrt (x + 8 + 2 * Real.sqrt (x + 7)) = Real.sqrt (x + 7) + 1 := h17
      linarith [h_eq, h33]
    -- Now, derive h_eq4 : Real.sqrt (x +1 - Real.sqrt (x +7)) =3 - Real.sqrt (x +7).
    have h_eq4 : Real.sqrt (x + 1 - Real.sqrt (x + 7)) = 3 - Real.sqrt (x + 7) := by
      nlinarith [h_eq3, Real.sqrt_nonneg (x + 1 - Real.sqrt (x + 7)), 
          Real.sqrt_nonneg (x + 7)]
    -- Prove x =2 from above.
    by_cases h22 : x + 1 - Real.sqrt (x + 7) ≥ 0
    · -- Assume x +1 - Real.sqrt (x +7) ≥0.
      have h23 : Real.sqrt (x + 1 - Real.sqrt (x + 7)) = 3 - Real.sqrt (x + 7) := h_eq4
      have h24 : (3 - Real.sqrt (x + 7)) ^ 2 = x +1 - Real.sqrt (x +7) := by 
        calc
          (3 - Real.sqrt (x + 7)) ^ 2 = (Real.sqrt (x + 1 - Real.sqrt (x + 7))) ^ 2 := by 
            rw [h23]
          _ = x + 1 - Real.sqrt (x +7) := by
            rw [Real.sq_sqrt]
            linarith
      have h25 : Real.sqrt (x + 7) =3 := by
        nlinarith [Real.sqrt_nonneg (x + 7), Real.sq_sqrt (show (0 : ℝ) ≤ x + 7 by linarith)]
      have h26 : x = 2 := by
        nlinarith [Real.sqrt_nonneg (x + 7), h25, Real.sq_sqrt (show (0 : ℝ) ≤ x + 7 by linarith)]
      exact_mod_cast h26
    · -- Assume x +1 - Real.sqrt (x +7) <0.
      have h31 : Real.sqrt (x + 1 - Real.sqrt (x + 7)) =0 := by
        rw [Real.sqrt_eq_zero'.mpr]
        linarith
      have h32 : 3 - Real.sqrt (x + 7) =0 := by
        linarith [h_eq4, h31]
      have h33 : Real.sqrt (x + 7) =3 := by
        linarith
      have h34 : x =2 := by 
        nlinarith [Real.sqrt_nonneg (x +7), h33, Real.sq_sqrt (show (0 : ℝ) ≤ x + 7 by linarith)]
      exact_mod_cast h34
  · -- Backward implication: if x=2, then the equation is satisfied.
    intro h_eq
    rw [h_eq]
    have h1 : Real.sqrt ( (2 : ℝ) + 8 + 2 * Real.sqrt ( (2 : ℝ) + 7) ) =4 := by 
      have h24 : ( (2 : ℝ) +8 +2 * Real.sqrt ( (2 : ℝ) +7 ) )= (16: ℝ ) := by
        have h241 : Real.sqrt (2 +7: ℝ ) =3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h241]
        all_goals norm_num
      rw [h24]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h5 : Real.sqrt ( (2 +1 - Real.sqrt (2 +7 ) ) ) =0 := by
      have h6 : Real.sqrt (2 +7 ) =3 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      have h7 : ( (2: ℝ )+1 - Real.sqrt (2 +7 ) )= (0: ℝ ) := by
        rw [h6]
        all_goals norm_num
      rw [h7]
      simp [Real.sqrt_eq_zero]
    rw [h1, h5]
    all_goals norm_num