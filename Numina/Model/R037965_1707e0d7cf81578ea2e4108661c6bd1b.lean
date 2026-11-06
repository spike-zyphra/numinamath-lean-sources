import Mathlib

open BigOperators Real Set

theorem algebra_163250 {a : ℝ} (ha : a > 0) (f : ℝ → ℝ) (hf : f = λ x => x + a / x)
  (hinc : MonotoneOn f (Set.Ioi (a - 2))) :
  a ≥ 4 := by
  by_contra h
  push_neg at h
  have h1 : a < 4 := by linarith
  have h9 : a - 2 < a / 2 := by
    nlinarith
  have h10 : a / 2 < Real.sqrt a := by
    have h5 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg a, sq_nonneg (Real.sqrt a - a / 2), Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)]
  have h11 : f (a / 2) > f (Real.sqrt a) := by
    rw [hf]
    have h12 : (a / 2 : ℝ) + a / (a / 2) > Real.sqrt a + a / Real.sqrt a := by
      have h14 : (a / 2 : ℝ) + a / (a / 2) = a / 2 + 2 := by
        field_simp
        <;> nlinarith
      have h15 : Real.sqrt a + a / Real.sqrt a = 2 * Real.sqrt a := by
        have h17 : a / Real.sqrt a = Real.sqrt a := by
          have h18 : Real.sqrt a > 0 := by
            positivity
          field_simp [Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)]
        nlinarith
      rw [h14, h15]
      have h16 : (Real.sqrt a - 2) ^ 2 > 0 := by
        have h17 : Real.sqrt a < (2 : ℝ) := by
          nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), h1]
        have h18 : Real.sqrt a > 0 := by
          positivity
        nlinarith
      have h17 : (a / 2 : ℝ) + 2 > 2 * Real.sqrt a := by
        nlinarith [Real.sqrt_nonneg a, Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), sq_nonneg (Real.sqrt a - 2)]
      linarith
    simpa using h12
  have h18 : f (a / 2) ≤ f (Real.sqrt a) := by
    apply hinc
    · -- Show that a/2 is in the interval
      simp
      nlinarith
    · -- Show that sqrt a is in the interval
      simp
      have h13 : Real.sqrt a > a - 2 := by
        by_contra h
        push_neg at h
        have h14 : Real.sqrt a ≤ a - 2 := by linarith
        have h15 : (Real.sqrt a) ^ 2 ≤ (a - 2) ^ 2 := by nlinarith [Real.sqrt_nonneg a, sq_nonneg (a - 2)]
        have h17 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith)
        nlinarith
      nlinarith
    all_goals
      try { nlinarith }
  linarith