import Mathlib

theorem algebra_99425 {x y : ℝ} (hx : x > 3) (hy : y > -4) :
    12 / Real.sqrt (x - 3) + 9 / Real.sqrt (y + 4) =
    18 - 3 * Real.sqrt (x - 3) - Real.sqrt (y + 4) ↔ x = 7 ∧ y = 5 := by
  constructor
  · -- Assume the equation holds, prove (x = 7 ∧ y = 5)
    intro h_eq
    have h1 : Real.sqrt (x - 3) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have h2 : Real.sqrt (y + 4) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    have eq1 : 12 / Real.sqrt (x - 3) + 3 * Real.sqrt (x - 3) + 9 / Real.sqrt (y + 4) + Real.sqrt (y + 4) = 18 := by
      nlinarith
    have h3 : 12 / Real.sqrt (x - 3) + 3 * Real.sqrt (x - 3) ≥ 12 := by
      have ha : Real.sqrt (x - 3) > 0 := h1
      have h31 : 12 / Real.sqrt (x - 3) + 3 * Real.sqrt (x - 3) - 12 ≥ 0 := by
        have h32 : 12 / Real.sqrt (x - 3) + 3 * Real.sqrt (x - 3) - 12 =
            (12 + 3 * (Real.sqrt (x - 3)) ^ 2 - 12 * Real.sqrt (x - 3)) / Real.sqrt (x - 3) := by
          field_simp
          <;> ring
        rw [h32]
        have h33 : (12 + 3 * (Real.sqrt (x - 3)) ^ 2 - 12 * Real.sqrt (x - 3)) ≥ 0 := by
          nlinarith [sq_nonneg (Real.sqrt (x - 3) - 2)]
        apply div_nonneg
        linarith
        linarith
      linarith
    have h4 : 9 / Real.sqrt (y + 4) + Real.sqrt (y + 4) ≥ 6 := by
      have hb : Real.sqrt (y + 4) > 0 := h2
      have h41 : 9 / Real.sqrt (y + 4) + Real.sqrt (y + 4) - 6 ≥ 0 := by
        have h42 : 9 / Real.sqrt (y + 4) + Real.sqrt (y + 4) - 6 =
            (9 + (Real.sqrt (y + 4)) ^ 2 - 6 * Real.sqrt (y + 4)) / Real.sqrt (y + 4) := by
          field_simp
          <;> ring
        rw [h42]
        have h43 : (9 + (Real.sqrt (y + 4)) ^ 2 - 6 * Real.sqrt (y + 4)) ≥ 0 := by
          nlinarith [sq_nonneg (Real.sqrt (y + 4) - 3)]
        apply div_nonneg
        linarith
        linarith
      linarith
    have eq2 : 12 / Real.sqrt (x - 3) + 3 * Real.sqrt (x - 3) = 12 := by
      nlinarith [eq1, h3, h4]
    have eq3 : Real.sqrt (x - 3) = 2 := by
      have ha : Real.sqrt (x - 3) > 0 := h1
      field_simp at eq2
      nlinarith [Real.sq_sqrt (show 0 ≤ (x - 3 : ℝ) by linarith)]
    have eq4 : 9 / Real.sqrt (y + 4) + Real.sqrt (y + 4) = 6 := by
      nlinarith [eq1, h3, h4]
    have eq5 : Real.sqrt (y + 4) = 3 := by
      have hb : Real.sqrt (y + 4) > 0 := h2
      field_simp at eq4
      nlinarith [Real.sq_sqrt (show 0 ≤ (y + 4 : ℝ) by linarith)]
    have eq6 : x - 3 = 4 := by
      calc
        x - 3 = (Real.sqrt (x - 3))  ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (2) ^ 2 := by
          rw [eq3]
        _ = (4 : ℝ) := by
          norm_num
    have eq7 : x = 7 := by
      linarith
    have eq8 : y + 4 = 9 := by
      calc
        y + 4 = (Real.sqrt (y + 4))  ^ 2 := by
          rw [Real.sq_sqrt]
          linarith
        _ = (3) ^ 2 := by
          rw [eq5]
        _ = (9 : ℝ) := by
          norm_num
    have eq9 : y = 5 := by
      linarith
    exact ⟨eq7, eq9⟩
  · -- Assume x = 7 and y = 5, prove the equation
    rintro ⟨hx, hy⟩
    have h1 : Real.sqrt (x - 3) = 2 := by
      rw [hx]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (y + 4) = 3 := by
      rw [hy]
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num