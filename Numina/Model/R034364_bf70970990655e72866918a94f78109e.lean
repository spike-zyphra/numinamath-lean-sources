import Mathlib

theorem inequalities_228004 (m n : ℤ) (hm : m > 0) (hn : n > 0)
    (h : ∀ x : ℝ, |m * x - 840| ≥ |x - n|) :
    m + n ≥ 58 := by
  by_contra h1
  push_neg at h1
  have h2 : (n : ℝ) = 840 / (m : ℝ) := by 
    have h3 := h (840 / (m : ℝ))
    have h4 : |(m : ℝ) * (840 / (m : ℝ)) - 840| ≥ |(840 / (m : ℝ) ) - (n : ℝ)| := by 
      simpa using h3
    have h5 : (m : ℝ) * (840 / (m : ℝ)) -840 = (0 : ℝ) := by 
      field_simp 
      <;> nlinarith 
    rw [h5] at h4
    have h6 : |(840 / (m : ℝ) ) - (n : ℝ)| ≤ (0 : ℝ) := by 
      simpa using h4
    have h7 : |(840 / (m : ℝ) ) - (n : ℝ)| = (0 : ℝ) := by
      linarith [abs_nonneg ((840 / (m : ℝ) ) - (n : ℝ)), h6]
    have h8 : (840 / (m : ℝ) ) - (n : ℝ) = 0 := by 
      simpa [abs_eq_zero] using h7
    linarith 
  have hn_eq : n * m = 840 := by
    have h8 : (n : ℝ) * (m : ℝ) = (840 : ℝ) := by
      have h9 : (n : ℝ) = 840 / (m : ℝ) := by
        linarith [h2]
      rw [h9]
      field_simp
      <;> nlinarith
    norm_cast at h8 ⊢
  have h9 : m ≤ 57 := by 
    nlinarith
  interval_cases m <;> omega