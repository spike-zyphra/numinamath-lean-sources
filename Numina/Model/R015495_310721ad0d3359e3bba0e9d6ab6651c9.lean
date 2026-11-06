import Mathlib

open Real

theorem algebra_310051 {r : ℝ} (hr : r ≥ 4) :
    (1 / r - 1 / (r + 1)) < (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) ∧
    (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) < (1 / (r * (Real.sqrt r + Real.sqrt (r + 1)))) := by
  have h1 : r ≥ 4 := hr
  have h2 : Real.sqrt r ≥ 2 := by
    have h3 : Real.sqrt 4 = 2 := Real.sqrt_eq_cases.mpr (by norm_num)
    have h4 : Real.sqrt r ≥ Real.sqrt 4 := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith [h3, h4]
  have h3 : Real.sqrt (r + 1) ≥ Real.sqrt 5 := by
    have h4 : r + 1 ≥ 5 := by linarith
    have h5 : Real.sqrt (r + 1) ≥ Real.sqrt 5 := by
      apply Real.sqrt_le_sqrt
      linarith
    linarith

  have ha1 : (1 / r - 1 / (r + 1)) = 1 / (r * (r + 1)) := by
    field_simp
    <;> ring

  have hb1 : (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) = (Real.sqrt (r + 1) - Real.sqrt r) / (Real.sqrt r * Real.sqrt (r + 1)) := by
    field_simp

  have h4 : (1 / r - 1 / (r + 1)) < (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) := by
    rw [ha1, hb1]
    have h5 : 0 < Real.sqrt r := by
      apply Real.sqrt_pos.mpr
      linarith
    have h6 : 0 < Real.sqrt (r + 1) := by
      apply Real.sqrt_pos.mpr
      linarith
    have h7 : Real.sqrt r * Real.sqrt (r + 1) > 0 := by positivity
    have h8 : r * (r + 1) > 0 := by positivity
    suffices (Real.sqrt (r + 1) - Real.sqrt r) / (Real.sqrt r * Real.sqrt (r + 1)) > 1 / (r * (r + 1)) by linarith
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg r, Real.sqrt_nonneg (r + 1), Real.sq_sqrt (show 0 ≤ (r : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (r + 1 : ℝ) by linarith), sq_nonneg (Real.sqrt r - 2), sq_nonneg (Real.sqrt (r + 1) - Real.sqrt r), sq_nonneg (r - 4), mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg (r + 1)), Real.sqrt_le_sqrt (show 4 ≤ r by linarith), Real.sqrt_le_sqrt (show r ≤ r + 1 by linarith)]

  have h10 : (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) < (1 / (r * (Real.sqrt r + Real.sqrt (r + 1)))) := by
    have hb1 : (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) = (Real.sqrt (r + 1) - Real.sqrt r) / (Real.sqrt r * Real.sqrt (r + 1)) := by
      field_simp
    rw [hb1]
    have h5 : 0 < Real.sqrt r := by
      apply Real.sqrt_pos.mpr
      linarith
    have h6 : 0 < Real.sqrt (r + 1) := by
      apply Real.sqrt_pos.mpr
      linarith
    have h7 : Real.sqrt r * Real.sqrt (r + 1) > 0 := by positivity
    have h8 : r * (Real.sqrt r + Real.sqrt (r + 1)) > 0 := by positivity
    suffices (Real.sqrt (r + 1) - Real.sqrt r) / (Real.sqrt r * Real.sqrt (r + 1)) < (1 / (r * (Real.sqrt r + Real.sqrt (r + 1)))) by linarith
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    have h9 : (Real.sqrt (r + 1) - Real.sqrt r) * (r * (Real.sqrt r + Real.sqrt (r + 1)) ) < (Real.sqrt r * Real.sqrt (r + 1)) := by
      have h10 : (Real.sqrt (r + 1) - Real.sqrt r) * (Real.sqrt (r + 1) + Real.sqrt r) = 1 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (r : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (r + 1 : ℝ) by linarith), sq_nonneg (Real.sqrt (r + 1) ^ 2 - Real.sqrt r ^ 2)]
      nlinarith [Real.sqrt_nonneg r, Real.sqrt_nonneg (r + 1), Real.sq_sqrt (show 0 ≤ (r : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (r + 1 : ℝ) by linarith), sq_nonneg (Real.sqrt r ^ 2 - r), sq_nonneg (Real.sqrt (r + 1) ^ 2 - (r + 1)), mul_nonneg (Real.sqrt_nonneg r) (Real.sqrt_nonneg (r + 1)), Real.sq_sqrt (show 0 ≤ (r + 1 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (r : ℝ) by linarith)]
    linarith

  constructor
  · exact h4
  · exact h10