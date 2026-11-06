import Mathlib

theorem algebra_43233 {a b c : ℝ} (h0 : a * b = 3) (h1 : a * c = 4) (h2 : b + c = 5)
    (q : ℚ) (h3 : b * c = q) : q.num + q.den = 349 := by
  have h4 : a * (b + c) = 7 := by
    calc
      a * (b + c) = a * b + a * c := by ring
      _ = 3 + 4 := by rw [h0, h1]
      _ = (7 : ℝ) := by norm_num
  have h5 : a = 7 / 5 := by
    rw [h2] at h4
    linarith
  have h6 : b = 15 / 7 := by 
    have h0' : a * b = 3 := h0
    rw [h5] at h0'
    linarith
  have h7 : c = 20 / 7 := by
    have h1' : a * c = 4 := h1
    rw [h5] at h1'
    linarith
  have h8 : b * c = 300 / 49 := by
    rw [h6, h7]
    norm_num
  have hq : q = (300 / 49 : ℚ) := by
    have hq1 : (b * c : ℝ) = (300 / 49 : ℝ) := by
      linarith [h8]
    have hq2 : (q : ℝ) = (300 / 49 : ℝ) := by
      linarith [h3, hq1]
    have hq3 : q = (300 / 49 : ℚ) := by 
      have hq4 : (q : ℝ) = (300 / 49 : ℝ) := hq2
      have hq5 : (q : ℝ) = ( (300 / 49 : ℚ) : ℝ ) := by
        norm_num at hq4 ⊢
        linarith
      exact_mod_cast hq5
    exact hq3
  rw [hq]
  native_decide