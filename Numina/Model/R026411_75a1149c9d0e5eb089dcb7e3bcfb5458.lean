import Mathlib

theorem inequalities_197723 (a b : ℝ) : |a + b| / (1 + |a + b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by 
  have h1 : |a + b| ≤ |a| + |b| := by
    apply abs_add
  have h5 : |a + b| ≤ |a| + |b| := h1
  have h2 : |a| ≥ 0 := abs_nonneg a
  have h3 : |b| ≥ 0 := abs_nonneg b
  have h4 : |a + b| ≥ 0 := abs_nonneg (a + b)
  have h6 : |a + b| / (1 + |a + b|) ≤ (|a| + |b|) / (1 + |a| + |b|) := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [h5, mul_nonneg (show 0 ≤ |a| by positivity) (show 0 ≤ |b| by positivity), sq_nonneg (|a| - |b|), sq_nonneg (|a + b| - |a|), sq_nonneg (|a + b| - |b|)]
  have h7 : (|a| + |b|) / (1 + |a| + |b|) ≤ |a| / (1 + |a|) + |b| / (1 + |b|) := by 
    have h8 : |a| ≥ 0 := abs_nonneg a 
    have h9 : |b| ≥ 0 := abs_nonneg b 
    have h10 : |a| + |b| ≥ 0 := by linarith 
    have h11 : 1 + |a| > 0 := by linarith 
    have h12 : 1 + |b| > 0 := by linarith 
    have h13 : 1 + |a| + |b| > 0 := by linarith 
    have h14 : |a| * |b| ≥ 0 := mul_nonneg (abs_nonneg a) (abs_nonneg b)
    have h15 : |a| / (1 + |a|) + |b| / (1 + |b|) = (|a| * (1 + |b|) + |b| * (1 + |a|)) / ((1 + |a|) * (1 + |b|)) := by
      field_simp 
      <;> ring 
    rw [h15] at *
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (|a| - |b|), mul_nonneg (show 0 ≤ |a| by positivity) (show 0 ≤ |b| by positivity), sq_nonneg (|a|), sq_nonneg (|b|)]
  linarith [h6, h7]