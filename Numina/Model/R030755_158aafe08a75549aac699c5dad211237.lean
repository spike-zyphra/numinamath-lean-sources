import Mathlib

theorem algebra_173770 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : c ≠ -a)
    (h1 : a + b + c = 7) (h2 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = 7 / 10) :
    a / (b + c) + b / (c + a) + c / (a + b) = 19 / 10 := by
  have h3 : a + b ≠ 0 := by
    intro h
    apply ha
    linarith
  have h4 : b + c ≠ 0 := by
    intro h
    apply hb
    linarith
  have h5 : c + a ≠ 0 := by
    intro h
    apply hc
    linarith
  have eq1 : (b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c) = 7 / 10 * ((a + b) * (b + c) * (c + a)) := by 
    have h6 : 1 / (a + b) + 1 / (b + c) + 1 / (c + a) = ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) := by
      field_simp [(show (a + b) ≠ 0 by assumption), (show (b + c) ≠ 0 by assumption), (show (c + a) ≠ 0 by assumption)]
      ring
    rw [h6] at h2
    have h7 : ((b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c)) / ((a + b) * (b + c) * (c + a)) = 7 / 10 := by
      linarith [h2]
    have h8 : (b + c) * (c + a) + (a + b) * (c + a) + (a + b) * (b + c) = 7 / 10 * ((a + b) * (b + c) * (c + a)) := by 
      field_simp [(show (a + b) * (b + c) * (c + a) ≠ 0 by 
        apply mul_ne_zero
        apply mul_ne_zero
        exact h3
        exact h4
        exact h5
      )] at h7 ⊢
      linarith [h7]
    linarith
  have eq2 : a / (b + c) + b / (c + a) + c / (a + b) =
      (a * (a + b) * (c + a) + b * (a + b) * (b + c) + c * (b + c) * (c + a)) / ((b + c) * (c + a) * (a + b)) := by
    field_simp [(show (b + c) ≠ 0 by assumption), (show (c + a) ≠ 0 by assumption), (show (a + b) ≠ 0 by assumption)]
    ring
  rw [eq2]
  have h8 : a * (a + b) * (c + a) + b * (a + b) * (b + c) + c * (b + c) * (c + a) = 19 / 10 * ((b + c) * (c + a) * (a + b)) := by
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), 
      sq_nonneg (a + b + c - 7), sq_pos_of_pos (show (10 : ℝ) > 0 by norm_num), 
      sq_nonneg ((a + b) * (b + c) * (c + a)), 
      h1, eq1, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)
    ]
  rw [h8]
  <;> field_simp [(show (b + c) * (c + a) * (a + b) ≠ 0 by
    apply mul_ne_zero
    apply mul_ne_zero
    exact h4
    exact h5
    exact h3
  )]
  <;> nlinarith [h1, eq1, h8]