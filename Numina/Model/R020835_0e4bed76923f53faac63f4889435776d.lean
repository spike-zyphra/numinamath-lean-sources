import Mathlib

theorem algebra_235318 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b + c = a * b * c) :
    a > 1 ∧ b > 1 ∨ b > 1 ∧ c > 1 ∨ a > 1 ∧ c > 1 := by 
  by_contra h1
  push_neg at h1
  have h1 : ¬(a > 1 ∧ b > 1 ∨ b > 1 ∧ c > 1 ∨ a > 1 ∧ c > 1) := by 
    simpa using h1
  have h2 : ¬(a > 1 ∧ b > 1) := by 
    intro h
    tauto
  have h3 : ¬(b > 1 ∧ c > 1) := by 
    intro h
    tauto
  have h4 : ¬(a > 1 ∧ c > 1) := by 
    intro h
    tauto 
  by_cases ha1 : a > 1
  · -- Assume a > 1, so b ≤ 1 and c ≤ 1
    have hb1 : b ≤ 1 := by 
      by_contra h5 
      push_neg at h5 
      have h2' : a > 1 ∧ b > 1 := ⟨ha1, h5⟩ 
      contradiction 
    have hc1 : c ≤ 1 := by
      by_contra h5 
      push_neg at h5 
      have h4' : a > 1 ∧ c > 1 := ⟨ha1, h5⟩ 
      contradiction 
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
              mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1), 
              mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  · -- Assume a ≤ 1
    have ha1 : a ≤ 1 := by linarith 
    by_cases hb1 : b > 1 
    · -- Assume b > 1, so a ≤ 1 and c ≤ 1 
      have ha1 : a ≤ 1 := by linarith 
      have hc1 : c ≤ 1 := by
        by_contra h5 
        push_neg at h5 
        have h3' : b > 1 ∧ c > 1 := ⟨hb1, h5⟩ 
        contradiction 
      nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1), 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
    · -- Assume b ≤ 1 
      have hb1 : b ≤ 1 := by linarith 
      by_cases hc1 : c > 1 
      · -- Assume c > 1, so a ≤ 1 and b ≤ 1 
        have ha1 : a ≤ 1 := by linarith 
        have hb1 : b ≤ 1 := by linarith 
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                  mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
      · -- Assume c ≤ 1 
        have hc1 : c ≤ 1 := by linarith 
        nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, 
                  mul_self_nonneg (a - 1), mul_self_nonneg (b - 1), mul_self_nonneg (c - 1), 
                  mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]