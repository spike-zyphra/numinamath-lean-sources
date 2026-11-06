import Mathlib

theorem algebra_264498 (d1 d2 d3 d4 d5 : ℝ)
    (h₀ : d1 > 0) (h₁ : d2 = 2 * d1) (h₂ : d3 = d2 / 2)
    (h₃ : d4 = d3 / 2) (h₄ : d5 = 2 * d4)
    (h₅ : min (min (min (min d1 d2) d3) d4) d5 = 5) :
    d1 + d2 + d3 + d4 + d5 = 55 := by
  have h6 : d2 = 2 * d1 := h₁
  have h7 : d3 = d1 := by
    rw [h₂, h6]
    all_goals linarith
  have h8 : d4 = d1 / 2 := by
    rw [h₃, h7]
    all_goals linarith
  have h9 : d5 = d1 := by 
    rw [h₄, h8]
    all_goals linarith
  have h10 : min (min (min (min d1 d2) d3) d4) d5 = d4 := by
    have h11 : min d1 d2 = d1 := by
      have h12 : d2 = 2 * d1 := h₁
      have h13 : d1 ≤ d2 := by
        nlinarith [h12, h₀]
      have h14 : min d1 d2 = d1 := by
        apply min_eq_left
        linarith
      linarith
    have h15 : min (min d1 d2) d3 = d1 := by
      rw [h11]
      have h16 : d3 = d1 := h7
      rw [h16]
      all_goals
        apply min_eq_left
        all_goals nlinarith
    have h17 : min (min (min d1 d2) d3) d4 = d4 := by
      rw [h15]
      all_goals
        have h18 : d4 = d1 / 2 := h8
        rw [h18]
        all_goals
          apply min_eq_right
          nlinarith
    have h18 : min (min (min (min d1 d2) d3) d4) d5 = d4 := by
      rw [h17]
      have h18 : d5 = d1 := h9
      rw [h18]
      all_goals
        have h19 : d4 = d1 / 2 := h8
        rw [h19]
        all_goals
          apply min_eq_left
          nlinarith
    linarith
  have h19 : d4 = 5 := by
    have eq1 : min (min (min (min d1 d2) d3) d4) d5 = 5 := h₅
    rw [h10] at eq1
    linarith
  have h20 : d1 = 10 := by
    linarith [h8, h19]
  have h21 : d2 = 20 := by
    rw [h20] at h6
    linarith
  have h22 : d3 = 10 := by
    rw [h20] at h7
    linarith
  have h24 : d5 = 10 := by
    have eq1 : d5 = d1 := by
      linarith [h9, h20]
    linarith [eq1, h20]
  linarith [h20, h21, h22, h19, h24]