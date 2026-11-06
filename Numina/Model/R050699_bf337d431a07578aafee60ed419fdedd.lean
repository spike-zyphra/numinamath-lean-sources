import Mathlib

theorem inequalities_303178
    (a b c : ℝ)
    (x y z : ℝ)
    (h₀ : 0 < a)
    (h₁ : 0 < b)
    (h₂ : 0 < c)
    (h₃ : a ≠ b)
    (h₄ : b ≠ c)
    (h₅ : c ≠ a)
    (h₆ : x = (b ^ 2 + 1) / a)
    (h₇ : y = (c ^ 2 + 1) / b)
    (h₈ : z = (a ^ 2 + 1) / c) :
    (x > 2 ∨ y > 2 ∨ z > 2) := by 
        by_contra h
        push_neg at h 
        have h9 : x ≤ 2 := by linarith
        have h10 : y ≤ 2 := by linarith
        have h11 : z ≤ 2 := by linarith
        have h12 : (b ^ 2 + 1) / a ≤ 2 := by 
            linarith [h9, h₆]
        have h13 : b ^ 2 + 1 ≤ 2 * a := by 
            have pos1 : 0 < a := h₀
            apply (div_le_iff₀ (by positivity)).mp at h12
            linarith 
        have h14 : (c ^ 2 + 1) / b ≤ 2 := by 
            linarith [h10, h₇]
        have h15 : c ^ 2 + 1 ≤ 2 * b := by 
            have pos2 : 0 < b := h₁
            apply (div_le_iff₀ (by positivity)).mp at h14
            linarith 
        have h16 : (a ^ 2 + 1) / c ≤ 2 := by 
            linarith [h11, h₈]
        have h17 : a ^ 2 + 1 ≤ 2 * c := by 
            have pos3 : 0 < c := h₂
            apply (div_le_iff₀ (by positivity)).mp at h16
            linarith 
        have h18 : (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 ≤ 0 := by 
            nlinarith [h13, h15, h17] 
        have ha1 : (a - 1) ^ 2 ≥ 0 := by nlinarith
        have hb1 : (b - 1) ^ 2 ≥ 0 := by nlinarith
        have hc1 : (c - 1) ^ 2 ≥ 0 := by nlinarith
        have ha2 : (a - 1) ^ 2 = 0 := by linarith [h18, ha1, hb1, hc1]
        have hb2 : (b - 1) ^ 2 = 0 := by linarith [h18, ha1, hb1, hc1]
        have hc2 : (c - 1) ^ 2 = 0 := by linarith [h18, ha1, hb1, hc1]
        have ha3 : a - 1 = 0 := by 
            rwa [sq_eq_zero_iff] at ha2 
        have hb3 : b - 1 = 0 := by 
            rwa [sq_eq_zero_iff] at hb2 
        have hc3 : c - 1 = 0 := by 
            rwa [sq_eq_zero_iff] at hc2 
        have ha4 : a = 1 := by linarith 
        have hb4 : b = 1 := by linarith 
        have heq : a = b := by linarith [ha4, hb4]
        exfalso 
        exact h₃ heq