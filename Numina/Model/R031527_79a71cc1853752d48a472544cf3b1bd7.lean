import Mathlib

/- Given $\frac{x}{{{x}^{2}}+x+1}=a\left( a\ne 0,a\ne \frac{1}{2} \right)$, then $\frac{{{x}^{2}}}{{{x}^{4}}+{{x}^{2}}+1}=$ ___          ___. -/
theorem algebra_4433
    {x a : ℝ}
    (hx : x ≠ 0)
    (h : x / (x ^ 2 + x + 1) = a)
    (ha : a ≠ 0 ∧ a ≠ 1 / 2) :
    x ^ 2 / (x ^ 4 + x ^ 2 + 1) = a ^ 2 / (1 - 2 * a) := by
  have h1 : x ^ 2 + x + 1 ≠ 0 := by 
    by_contra h1
    have h2 : x / (x ^ 2 + x + 1) = 0 := by
      rw [h1]
      norm_num
      all_goals linarith
    have h3 : a = 0 := by
      linarith [h, h2]
    have h4 : a = 0 := by 
      linarith
    have h5 : a ≠ 0 := ha.1
    contradiction
  have h2 : x = a * (x^2 + x + 1) := by 
    have h3 : x ^ 2 + x + 1 ≠ 0 := h1
    field_simp [h3] at h 
    linarith 
  have h3 : x^4 + x^2 + 1 = (x^2 + 1 - x) * (x^2 + 1 + x) := by 
    ring 
  have h4 : x^2 + 1 + x = x / a := by 
    have h3 : a ≠ 0 := ha.1 
    field_simp at *
    nlinarith [h2, sq_pos_of_ne_zero ha.1]
  have h5 : x^2 + 1 - x = x * (1 - 2 * a) / a := by 
    have h3 : a ≠ 0 := ha.1 
    field_simp at *
    nlinarith [h2, sq_pos_of_ne_zero ha.1]
  have h6 : x^4 + x^2 + 1 = x^2 * (1 - 2 * a) / a^2 := by 
    rw [h3]
    rw [h4, h5]
    <;> field_simp [ha.1] <;> ring_nf <;> nlinarith [h2, sq_pos_of_ne_zero (show a ≠ 0 by tauto)]
  rw [h6]
  have h7 : a ≠ 0 := ha.1
  have h8 : 1 - 2 * a ≠ 0 := by
    intro h9
    have h10 : a = 1 / 2 := by linarith 
    tauto 
  field_simp [h7, h8, sq_pos_of_ne_zero (show x ≠ 0 by exact hx), sq_pos_of_ne_zero h7]
  <;> ring_nf <;> nlinarith [h2, sq_pos_of_ne_zero h7, sq_pos_of_ne_zero (show x ≠ 0 by exact hx)]