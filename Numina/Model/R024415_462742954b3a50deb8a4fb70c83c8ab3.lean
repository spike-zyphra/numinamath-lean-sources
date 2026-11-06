import Mathlib

theorem algebra_181727 (a b : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x ^ 2 + a * x + b) :
    max (max (|f 1|) (|f 2|)) (|f 3|) ≥ 1 / 2 := by
  by_contra h
  push_neg at h
  have h1 : f 1 = 1 ^ 2 + a * 1 + b := by rw [hf]
  have h2 : f 2 = 2 ^ 2 + a * 2 + b := by rw [hf]
  have h3 : f 3 = 3 ^ 2 + a * 3 + b := by rw [hf]
  have h1' : |f 1| < 1 / 2 := by
    have h11 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h12 : |f 1| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  have h2' : |f 2| < 1 / 2 := by
    have h21 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h22 : |f 2| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  have h3' : |f 3| < 1 / 2 := by
    have h31 : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h32 : |f 3| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  rw [h1] at h1'
  rw [h2] at h2'
  rw [h3] at h3'
  have ineq1 : -(1 / 2) < (1 ^ 2 + a * 1 + b : ℝ) := by
    linarith [abs_lt.mp h1']
  have ineq1' : (1 ^ 2 + a * 1 + b : ℝ) < (1 / 2 : ℝ) := by
    linarith [abs_lt.mp h1']
  have ineq2 : -(1 / 2) < (2 ^ 2 + a * 2 + b : ℝ) := by
    linarith [abs_lt.mp h2']
  have ineq2' : (2 ^ 2 + a * 2 + b : ℝ) < (1 / 2 : ℝ) := by
    linarith [abs_lt.mp h2']
  have ineq3 : -(1 / 2) < (3 ^ 2 + a * 3 + b : ℝ) := by
    linarith [abs_lt.mp h3']
  have ineq3' : (3 ^ 2 + a * 3 + b : ℝ) < (1 / 2 : ℝ) := by
    linarith [abs_lt.mp h3']
  -- Simplify all the inequalities
  have ineq1_simplified : -3 / 2 < a + b := by
    nlinarith
  have ineq1'_simplified : a + b < -1 / 2 := by
    nlinarith
  have ineq2_simplified : -9 / 2 < 2 * a + b := by
    nlinarith
  have ineq2'_simplified : 2 * a + b < -7 / 2 := by
    nlinarith
  have ineq3_simplified : -19 / 2 < 3 * a + b := by
    nlinarith
  have ineq3'_simplified : 3 * a + b < -17 / 2 := by
    nlinarith
  -- Derive a contradiction from these constraints
  have ineq4 : a < -5 := by
    nlinarith
  have ineq5 : a > -5 := by
    nlinarith
  linarith