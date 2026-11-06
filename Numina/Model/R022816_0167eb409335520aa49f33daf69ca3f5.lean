import Mathlib

theorem inequalities_3137 (a b : ℝ) : |a| / (|a| + 2008) + |b| / (|b| + 2008) ≥ |a - b| / (2008 + |a - b|) := by
  have h1 : |a| + 2008 > 0 := by
    linarith [abs_nonneg a]
  have h2 : |b| + 2008 > 0 := by
    linarith [abs_nonneg b]
  have h3 : 2008 + |a - b| > 0 := by
    linarith [abs_nonneg (a - b)]
  have h5 : |a| / (|a| + 2008) + |b| / (|b| + 2008) - |a - b| / (2008 + |a - b|) ≥ 0 := by
    have h6 : |a| / (|a| + 2008) + |b| / (|b| + 2008) - |a - b| / (2008 + |a - b|) =
          (|a| * (|b| + 2008) * (2008 + |a - b|) + |b| * (|a| + 2008) * (2008 + |a - b|) - |a - b| * (|a| + 2008) * (|b| + 2008)) / ((|a| + 2008) * (|b| + 2008) * (2008 + |a - b|)) := by
      field_simp
      <;> ring
    rw [h6]
    have h4 : 0 < (|a| + 2008) * (|b| + 2008) * (2008 + |a - b|) := by
      positivity
    have h7 : |a| * (|b| + 2008) * (2008 + |a - b|) + |b| * (|a| + 2008) * (2008 + |a - b|) - |a - b| * (|a| + 2008) * (|b| + 2008) ≥ 0 := by
      have h8 : |a - b| ≤ |a| + |b| := by
        apply abs_sub
      nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|a| - |a - b|), sq_nonneg (|b| - |a - b|), 
                  abs_nonneg a, abs_nonneg b, abs_nonneg (a - b), 
                  h8, mul_nonneg (abs_nonneg a) (abs_nonneg b), 
                  mul_nonneg (abs_nonneg a) (abs_nonneg (a - b)), 
                  mul_nonneg (abs_nonneg b) (abs_nonneg (a - b))]
    apply div_nonneg
    linarith
    all_goals positivity
  linarith [h5]