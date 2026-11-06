import Mathlib

theorem algebra_190469 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : a < b) (h2 : b < c) (h3 : a + b + c = 21 / 4) (h4 : 1 / a + 1 / b + 1 / c = 21 / 4)
    (h5 : a * b * c = 1) :
    a = 1 / 4 ∧ b = 1 ∧ c = 4 := by
  -- Step 1: transformations of h4 from $\frac{1}{a} + \frac{1}{b} + \frac{1}{c} = \frac{21}{4}$ multiplied by product a * b * c =1 becomes the sum on b * c + a * c + a * b which is total $A + \cdots * 1$
  have eq1 : b * c + a * c + a * b = 21 / 4 := by 
    have h7 : a * b * c = 1 := h5
    have eq1 : 1 / a + 1 / b + 1 / c = 21 / 4 := h4
    have eq2 : 1 / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
      field_simp [ha, hb, hc]
      <;> ring
    rw [eq2] at eq1
    rw [h5] at eq1
    linarith
  have h8 : (a - 1 / 4) * (a - 1) * (a - 4) = 0 := by
    nlinarith [sq_nonneg (a - 1 / 4), sq_nonneg (a - 1), sq_nonneg (a - 4), 
          sq_nonneg (b - 1), sq_nonneg (c - 4), 
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), h3, eq1, h5, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc
    ]
  cases' (mul_eq_zero.mp h8) with h9 h10
  cases' (mul_eq_zero.mp h9) with h11 h12
  · -- $a - 1/4 = 0$, so $a = 1/4$
    have ha1 : a = 1 / 4 := by linarith
    have h13 : b = 1 := by 
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc
      ]
    have h14 : c = 4 := by 
      nlinarith [sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc
      ]
    exact ⟨ha1, h13, h14⟩
  · -- case $a = 1$
    have ha2 : a = 1 := by linarith
    nlinarith
  · -- step For right root in intercepts.
    have ha3 : a = 4 := by linarith
    nlinarith