import Mathlib

theorem algebra_166630 {m n : ℝ} (f : ℝ → ℝ) (hf : f = fun x => x^2 + m * x + n)
    (h1 : f m = m) (h2 : f n = n) :
    (m = 0 ∧ n = 0) ∨ (m = 1 / 2 ∧ n = 0) ∨ (m = 1 ∧ n = -1) := by
  have eq1 : f m = m ^ 2 + m * m + n := by 
    rw [hf]
  have eq2 : f n = n ^ 2 + m * n + n := by
    rw [hf]
  rw [eq1] at h1
  rw [eq2] at h2
  have eq3 : 2 * m ^ 2 + n = m := by
    nlinarith
  have eq4 : n * (n + m) = 0 := by
    nlinarith 
  cases' (mul_eq_zero.mp eq4) with h5 h6
  · -- Case n = 0
    have hn0 : n = 0 := h5
    have eq6 : 2 * m ^ 2 = m := by 
      rw [hn0] at eq3
      linarith 
    have eq7 : m * (2 * m - 1) = 0 := by
      linarith [eq6] 
    cases' (mul_eq_zero.mp eq7) with eq8 eq9
    · -- m = 0 
      left
      constructor
      · linarith
      · exact hn0
    · -- 2 * m - 1 = 0
      right 
      left 
      constructor 
      · linarith 
      · exact hn0
  · -- Case n + m = 0
    have eq10 : n = -m := by 
      linarith 
    have eq11 : 2 * m ^ 2 - 2 * m = 0 := by
      rw [eq10] at eq3
      linarith
    have eq12 : 2 * m * (m - 1) = 0 := by
      linarith [eq11]
    cases' (mul_eq_zero.mp eq12) with eq13 eq14
    · -- 2 * m = 0
      have hm0 : m = 0 := by 
        linarith
      have hn0 : n = 0 := by
        rw [hm0] at eq10
        linarith 
      left 
      constructor
      · -- m = 0
        linarith
      · -- n = 0
        linarith
    · -- m - 1 = 0
      have hm1 : m = 1 := by 
        linarith
      have hn1 : n = -1 := by
        rw [hm1] at eq10
        linarith
      right
      right 
      constructor 
      · -- m = 1
        linarith 
      · -- n = -1
        linarith