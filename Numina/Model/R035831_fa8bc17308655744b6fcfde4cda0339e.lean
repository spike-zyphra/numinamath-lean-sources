import Mathlib

theorem algebra_21574     (a b c d : ℚ)
    -- h₀: 所有时间都是正数
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    -- h₁: b + c + d = 3a (第一个条件)
    (h₁ : b + c + d = 3 * a)
    -- h₂: a + c + d = 4b (第二个条件)
    (h₂ : a + c + d = 4 * b)
    -- h₃: a + b + d = 2c (第三个条件)
    (h₃ : a + b + d = 2 * c)
    -- h₄: 8a + 10b + 6c = 24分钟 (2/5小时 = 24分钟)
    (h₄ : 8 * a + 10 * b + 6 * c = 2 / 5 * 60) :
    -- 结论：d表示为最简分数时，分子加分母等于28
    d.num + d.den = 28 := by

  have h5 : 4 * a = 5 * b := by
    linarith

  have h6 : 4 * a = 3 * c := by
    linarith

  have h7 : 5 * b = 3 * c := by
    linarith [h5, h6]

  have h8 : a = 1 := by
    have ha : 8 * a + 10 * b + 6 * c = 24 := by
      linarith
    have hb : b = 4 * a / 5 := by
      linarith
    have hc : c = 4 * a / 3 := by
      linarith
    rw [hb, hc] at ha
    linarith

  have ha1 : a = 1 := h8

  have hb1 : b = 4 / 5 := by 
    linarith [h5, ha1]

  have hc1 : c = 4 / 3 := by 
    linarith [h6, ha1]

  have hd1 : d = 13 / 15 := by 
    linarith [h₁, ha1, hb1, hc1]

  rw [hd1]
  native_decide