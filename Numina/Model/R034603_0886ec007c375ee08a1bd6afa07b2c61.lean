import Mathlib

theorem algebra_307172 {a b c : ℝ} (ha : a ≠ -1) (hb : b ≠ -2) (hc : c ≠ -3)
    (h1 : a + b + c = 0) (h2 : 1 / (a + 1) + 1 / (b + 2) + 1 / (c + 3) = 0) :
    (a + 1)^2 + (b + 2)^2 + (c + 3)^2 = 36 := by
  have ha1 : a + 1 ≠ 0 := by
    intro h
    apply ha
    linarith
  have hb1 : b + 2 ≠ 0 := by
    intro h
    apply hb
    linarith
  have hc1 : c + 3 ≠ 0 := by
    intro h
    apply hc
    linarith
  have h3 : (b + 2) * (c + 3) + (a + 1) * (c + 3) + (a + 1) * (b + 2) = 0 := by
    have eq1 : 1 / (a + 1) + 1 / (b + 2) + 1 / (c + 3) = 
          ( (b + 2) * (c + 3) + (a + 1) * (c + 3) + (a + 1) * (b + 2) ) / ( (a + 1) * (b + 2) * (c + 3) ) := by 
      field_simp [ha1, hb1, hc1]
      <;> ring
    rw [eq1] at h2
    have denom_ne_zero : (a + 1) * (b + 2) * (c + 3) ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      · exact ha1
      · exact hb1
      · exact hc1
    field_simp [denom_ne_zero] at h2 ⊢
    all_goals linarith
  have h4 : (a + 1) + (b + 2) + (c + 3) = 6 := by
    nlinarith
  -- Calculate $(a + 1)^2 + (b + 2)^2 + (c + 3)^2$.
  have h40 : (a + 1)^2 + (b + 2)^2 + (c + 3)^2 = ( (a + 1) + (b + 2) + (c + 3) )^2 - 2 * ((b + 2) * (c + 3) + (a + 1) * (c + 3) + (a + 1) * (b + 2)) := by 
    ring
  rw [h40]
  rw [h4, h3]
  all_goals norm_num