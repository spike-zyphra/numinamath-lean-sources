import Mathlib

theorem algebra_178477 (a b c d : ℤ) (h₀ : 0 ≤ a ∧ a ≤ 9) (h₁ : 0 ≤ b ∧ b ≤ 9)
    (h₂ : 0 ≤ c ∧ c ≤ 9) (h₃ : 0 ≤ d ∧ d ≤ 9) (h₄ : 6 * a + 9 * b + 3 * c + d = 88)
    (h₅ : a - b + c - d = -6) (h₆ : a - 9 * b + 3 * c - d = -46) :
    1000 * a + 100 * b + 10 * c + d = 6507 := by

  have h7 : a ≤ 9 := h₀.right
  have h8 : 0 ≤ a := h₀.left
  have h9 : b ≤ 9 := h₁.right
  have h10 : 0 ≤ b := h₁.left
  have h11 : c ≤ 9 := h₂.right
  have h12 : 0 ≤ c := h₂.left
  have h13 : d ≤ 9 := h₃.right
  have h14 : 0 ≤ d := h₃.left

  have h7_eq : c = 4 * b - 20 := by 
    omega
  
  have hb1 : b = 5 ∨ b = 6 ∨ b = 7 := by
    omega
  
  rcases hb1 with hb | hb | hb
  · -- b = 5
    rw [hb] at h7_eq
    -- c = 0
    have hc0 : c = 0 := by linarith

    -- From h₅: a - 5 + 0 - d = -6 => a - d = -1
    have h8_eq : a = d - 1 := by
      rw [hb, hc0] at h₅
      omega

    have hd7 : d = 7 := by
      rw [hb, hc0, h8_eq] at h₄
      omega

    have ha6 : a = 6 := by
      linarith

    linarith [hd7, ha6, hc0, hb]

  · -- b = 6
    rw [hb] at h7_eq
    -- c = 4
    have hc4 : c = 4 := by linarith

    -- From h₅: a - 6 + 4 - d = -6 => a - d = -4
    have h8_eq : a = d - 4 := by
      rw [hb, hc4] at h₅
      omega

    -- Substitute into h₄
    -- 6a + 9 * 6 + 3 * 4 + d = 88
    -- 6(d - 4) + 54 + 12 + d = 88
    -- 6d - 24 + 54 + 12 + d = 88
    -- 7d + 42 = 88
    -- 7d = 46
    -- d = 46 / 7
    -- Not integer solution, invalid
    rw [hb, hc4, h8_eq] at h₄
    omega

  · -- b = 7
    rw [hb] at h7_eq
    -- c = 8
    have hc8 : c = 8 := by linarith

    -- From h₅: a - 7 + 8 - d = -6 => a - d = -1
    have h8_eq : a = d - 7 := by
      rw [hb, hc8] at h₅
      omega

    -- Substitute into h₄
    -- 6a + 9 * 7 + 3 * 8 + d = 88
    -- 6(d - 7) + 63 + 24 + d = 88
    -- 6d - 42 + 63 + 24 + d = 88
    -- 7d + 45 = 88
    -- 7d = 43
    -- d = 43 / 7
    -- Not integer solution, invalid
    rw [hb, hc8, h8_eq] at h₄
    omega