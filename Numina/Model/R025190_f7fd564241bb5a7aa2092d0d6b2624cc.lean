import Mathlib

theorem inequalities_599055 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : ¬(a = 0 ∧ b = 0)) (h' : ¬(a = 0 ∧ c = 0)) (h'' : ¬(b = 0 ∧ c = 0)) :
    1 / (b + c) + 1 / (c + a) + 1 / (a + b) ≥
    a / (a ^ 2 + b * c) + b / (b ^ 2 + c * a) + c / (c ^ 2 + a * b) := by

  have hb1 : b + c > 0 := by
    by_contra h1
    push_neg at h1
    have hb2 : b = 0 := by linarith [hb, h1]
    have hc2 : c = 0 := by linarith [hc, h1]
    have h3 : b = 0 ∧ c = 0 := ⟨hb2, hc2⟩
    tauto

  have hc1 : c + a > 0 := by
    by_contra h1
    push_neg at h1
    have hc2 : c = 0 := by linarith [hc, h1]
    have ha2 : a = 0 := by linarith [ha, h1]
    have h3 : a = 0 ∧ c = 0 := ⟨ha2, hc2⟩
    tauto

  have ha1 : a + b > 0 := by
    by_contra h1
    push_neg at h1
    have ha2 : a = 0 := by linarith [ha, h1]
    have hb2 : b = 0 := by linarith [hb, h1]
    have h3 : a = 0 ∧ b = 0 := ⟨ha2, hb2⟩
    tauto

  have hb4 : a ^ 2 + b * c > 0 := by
    by_contra h1
    push_neg at h1
    have hb2 : a = 0 := by nlinarith [sq_nonneg (a), mul_nonneg hb hc]
    have hb3 : b * c = 0 := by nlinarith
    cases' (mul_eq_zero.mp hb3) with hb4 hc4
    · -- Case where b = 0
      have hb5 : b = 0 := by linarith
      have hb6 : a = 0 ∧ b = 0 := ⟨hb2, hb5⟩
      tauto
    · -- Case where c = 0
      have hc5 : c = 0 := by linarith
      have hc6 : a = 0 ∧ c = 0 := ⟨hb2, hc5⟩
      tauto

  have hb3 : b ^ 2 + c * a > 0 := by
    by_contra h1
    push_neg at h1
    have hb2 : b = 0 := by nlinarith [sq_nonneg (b), mul_nonneg ha hc]
    have hb3 : c * a = 0 := by nlinarith
    cases' (mul_eq_zero.mp hb3) with hc4 ha4
    · -- Case where c = 0
      have hc5 : c = 0 := by linarith
      have hc6 : b = 0 ∧ c = 0 := ⟨hb2, hc5⟩
      tauto
    · -- Case where a = 0
      have ha2 : a = 0 := by linarith
      have ha6 : a = 0 ∧ b = 0 := ⟨ha2, hb2⟩
      tauto

  have hb5 : c ^ 2 + a * b > 0 := by
    by_contra h1
    push_neg at h1
    have hb2 : c = 0 := by nlinarith [sq_nonneg (c), mul_nonneg ha hb]
    have hb3 : a * b = 0 := by nlinarith
    cases' (mul_eq_zero.mp hb3) with ha4 hb4
    · -- Case where a = 0
      have ha2 : a = 0 := by linarith
      have ha6 : a = 0 ∧ c = 0 := ⟨ha2, hb2⟩
      tauto
    · --  Case where b = 0
      have hb5 : b = 0 := by linarith
      have hb6 : b = 0 ∧ c = 0 := ⟨hb5, hb2⟩
      tauto

  have h1 : 1 / (b + c) + 1 / (c + a) + 1 / (a + b) - (a / (a ^ 2 + b * c) + b / (b ^ 2 + c * a) + c / (c ^ 2 + a * b)) ≥ 0 := by
    have hb3 : 0 < (b + c) * (c + a) * (a + b) * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) := by
      positivity
    have h3 : 1 / (b + c) + 1 / (c + a) + 1 / (a + b) - (a / (a ^ 2 + b * c) + b / (b ^ 2 + c * a) + c / (c ^ 2 + a * b)) =
        (( (a ^ 2 + b * c) * (c + a) * (a + b) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + (b + c) * (a ^ 2 + b * c) * (a + b) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + (b + c) * (c + a) * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) - (a * (b + c) * (c + a) * (a + b) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + b * (b + c) * (c + a) * (a + b) * (a ^ 2 + b * c) * (c ^ 2 + a * b) + c * (b + c) * (c + a) * (a + b) * (a ^ 2 + b * c) * (b ^ 2 + c * a)) ) ) / ((b + c) * (c + a) * (a + b) * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b)) := by
      field_simp
      ring
    rw [h3] at *
    apply div_nonneg
    nlinarith [sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b),
      sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      sq_nonneg (a * (a - b)), sq_nonneg (a * (a - c)), 
      sq_nonneg (b * (b - a)), sq_nonneg (b * (b - c)), 
      sq_nonneg (c * (c - a)), sq_nonneg (c * (c - b)), 
      mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc, 
      mul_nonneg (show 0 ≤ a * b from mul_nonneg ha hb) (show 0 ≤ b * c from mul_nonneg hb hc), 
      mul_nonneg (show 0 ≤ b * c from mul_nonneg hb hc) (show 0 ≤ c * a from mul_nonneg hc ha), 
      mul_nonneg (show 0 ≤ c * a from mul_nonneg hc ha) (show 0 ≤ a * b from mul_nonneg ha hb)
      ]
    positivity

  linarith