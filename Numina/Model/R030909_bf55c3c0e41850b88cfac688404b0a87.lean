import Mathlib

theorem algebra_255808 {a b c : ℚ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b = 1 / c) :
    ∃ q : ℚ, Real.sqrt (a ^ 2 + b ^ 2 + c ^ 2) = q := by
  have eq1 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b - c) ^ 2 := by
    have h2 : a * b = a * c + b * c := by
      field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm] at h ⊢
      nlinarith
    have h_eq1 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b - c) ^ 2 := by
      nlinarith [h2]
    exact h_eq1
  use (a + b - c)
  have h3 : (↑a : ℝ) ^ 2 + (↑b : ℝ) ^ 2 + (↑c : ℝ) ^ 2 = (↑(a + b - c) : ℝ) ^ 2 := by
    have h7 : (↑a : ℝ) ^ 2 + (↑b : ℝ) ^ 2 + (↑c : ℝ) ^ 2 = (↑(a ^ 2 + b ^ 2 + c ^ 2) : ℝ) := by
      simp
      <;> norm_num
      <;> ring_nf
      <;> norm_num
    have eq3 : (↑(a ^ 2 + b ^ 2 + c ^ 2) : ℝ) = (↑(a + b - c : ℚ) : ℝ) ^ 2 := by
      have eq4 : a ^ 2 + b ^ 2 + c ^ 2 = (a + b - c) ^ 2 := eq1
      have eq5 : (↑(a ^ 2 + b ^ 2 + c ^ 2) : ℝ) = (↑((a + b - c : ℚ) ^ 2) : ℝ) := by exact_mod_cast eq4
      have eq6 : (↑((a + b - c : ℚ) ^ 2) : ℝ) = (↑(a + b - c : ℚ) : ℝ) ^ 2 := by
        simp [Rat.cast_pow]
      rw [eq5, eq6]
      <;> norm_num
    have eq5 : (↑a : ℝ) ^ 2 + (↑b : ℝ) ^ 2 + (↑c : ℝ) ^ 2 = (↑(a + b - c : ℚ) : ℝ) ^ 2 := by
      linarith [h7, eq3]
    norm_num at eq5 ⊢
    exact_mod_cast eq5
  have h4 : Real.sqrt ((↑a : ℝ) ^ 2 + (↑b : ℝ) ^ 2 + (↑c : ℝ) ^ 2) = (↑(a + b - c) : ℝ) := by
    have h6 : Real.sqrt ((↑a : ℝ) ^ 2 + (↑b : ℝ) ^ 2 + (↑c : ℝ) ^ 2) = Real.sqrt ((↑(a + b - c : ℚ) : ℝ) ^ 2) := by
      rw [h3]
    rw [h6]
    have h8 : Real.sqrt ((↑(a + b - c : ℚ) : ℝ) ^ 2) = abs ((↑(a + b - c : ℚ) : ℝ)) := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h8]
    have h11 : (↑(a + b - c : ℚ) : ℝ) ≥ 0 := by
      have h111 : (a + b - c : ℚ) ≥ (0 : ℚ) := by 
        have h2 : a * b = a * c + b * c := by
          field_simp [ha.ne.symm, hb.ne.symm, hc.ne.symm] at h ⊢
          nlinarith
        nlinarith [show 0 < a by linarith, show 0 < b by linarith, show 0 < c by linarith, h2]
      have h112 : (↑(a + b - c : ℚ) : ℝ) ≥ (0 : ℝ) := by
        exact_mod_cast h111
      exact h112
    rw [abs_of_nonneg h11]
    all_goals linarith
  simpa using h4