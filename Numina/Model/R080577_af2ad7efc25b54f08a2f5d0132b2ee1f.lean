import Mathlib

theorem number_theory_116399
    (a1 a2 a3 b1 b2 b3 : ℝ)
    (h₀ : 0 < b1)
    (h₁ : 0 < b2)
    (h₂ : 0 < b3)
    (h₃ : a1 / b1 < a2 / b2)
    (h₄ : a2 / b2 < a3 / b3) :
    a1 / b1 < (a1 + a2 + a3) / (b1 + b2 + b3) ∧
    (a1 + a2 + a3) / (b1 + b2 + b3) < a3 / b3 := by
  have h5 : a1 * b2 < a2 * b1 := by
    have h6 : a1 / b1 < a2 / b2 := h₃
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h6
    linarith
  
  have h6 : a2 * b3 < a3 * b2 := by
    have h7 : a2 / b2 < a3 / b3 := h₄
    apply (div_lt_div_iff (by positivity) (by positivity)).mp at h7
    linarith
  
  have h7 : a1 / b1 < (a1 + a2 + a3) / (b1 + b2 + b3) := by
    have h_pos1 : 0 < b1 := h₀
    have h_pos2 : 0 < b2 := h₁
    have h_pos3 : 0 < b3 := h₂
    have h_pos4 : 0 < b1 + b2 + b3 := by linarith
    -- rewrite inequality $\frac{a_1}{b_1} < \frac{a_1 + a_2 + a_3}{b_1 + b_2 + b_3}$
    -- to $a_1 * (b_1 + b_2 + b_3) < (a_1 + a_2 + a_3) * b_1$ cross multiplying all denominators positive
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    -- nlinarith works with expressions involving nonlinear equalities and linear inequalities
    -- using algebra we proved the inequality.
    nlinarith [h5, h6, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]

  have h8 : (a1 + a2 + a3) / (b1 + b2 + b3) < a3 / b3 := by
    have h_pos1 : 0 < b1 := h₀
    have h_pos2 : 0 < b2 := h₁
    have h_pos3 : 0 < b3 := h₂
    have h_pos4 : 0 < b1 + b2 + b3 := by linarith
    -- rewrite inequality $\frac{a_1 + a_2 + a_3}{b_1 + b_2 + b_3} < \frac{a_3}{b_3}$
    -- to $(a_1 + a_2 + a_3) * b_3 < a_3 * (b_1 + b_2 + b_3)$ cross multiplying all denominators positive
    apply (div_lt_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h5, h6, mul_pos h₀ h₁, mul_pos h₀ h₂, mul_pos h₁ h₂]

  constructor
  · exact h7
  · exact h8