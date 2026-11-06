import Mathlib

theorem algebra_209526 (p q : ℝ) (f : ℝ → ℝ) (hf : f = fun x => x^2 + p * x + q) :
    max (max (|f 1|) (|f 2|)) (|f 3|) ≥ 1 / 2 := by
  have h1 : f 1 = 1 ^ 2 + p * 1 + q := by simp [hf]
  have h2 : f 2 = 2 ^ 2 + p * 2 + q := by simp [hf]
  have h3 : f 3 = 3 ^ 2 + p * 3 + q := by simp [hf]
  have eq1 : f 1 = 1 + p + q := by
    rw [h1]
    all_goals ring
  have eq2 : f 2 = 4 + 2 * p + q := by
    rw [h2]
    all_goals ring
  have eq3 : f 3 = 9 + 3 * p + q := by
    rw [h3]
    all_goals ring
  by_contra h
  push_neg at h
  have h11 : |f 1| < 1 / 2 := by
    have h1' : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h11 : |f 1| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  have h22 : |f 2| < 1 / 2 := by
    have h1' : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h33 : |f 2| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  have h33 : |f 3| < 1 / 2 := by
    have h1' : max (max (|f 1|) (|f 2|)) (|f 3|) < 1 / 2 := h
    have h44 : |f 3| ≤ max (max (|f 1|) (|f 2|)) (|f 3|) := by
      simp [max_le_iff]
    linarith
  rw [eq1] at h11
  rw [eq2] at h22
  rw [eq3] at h33
  have h111 : -(1 / 2) < 1 + p + q := by  linarith [abs_lt.mp h11]
  have h112 : 1 + p + q < 1 / 2 := by  linarith [abs_lt.mp h11]
  have h211 : -(1 / 2) < 4 + 2 * p + q := by  linarith [abs_lt.mp h22]
  have h212 : 4 + 2 * p + q < 1 / 2 := by  linarith [abs_lt.mp h22]
  have h311 : -(1 / 2) < 9 + 3 * p + q := by  linarith [abs_lt.mp h33]
  have h312 : 9 + 3 * p + q < 1 / 2 := by  linarith [abs_lt.mp h33]
  have hp1 : -4 < p := by
    nlinarith
  have hp2 : p < -4 := by
    nlinarith
  linarith