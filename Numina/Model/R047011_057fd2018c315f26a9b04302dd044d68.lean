import Mathlib

theorem algebra_208306 :
  { (x, y) : ℤ × ℤ |
    x + y = x^2 - x * y + y^2 }
  =
  { (2, 1), (1, 2), (0, 0), (2, 2), (1, 0), (0, 1) } := by 
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume h : x + y = x^2 - x * y + y^2, prove ( (x, y) ∈ ({ (2, 1), (1, 2), (0, 0), (2, 2), (1, 0), (0, 1) }) )
    rintro h
    have h1 : (x - y) ^ 2 + (x - 1) * (y - 1) = 1 := by
      nlinarith
    have h2 : (x - y) ^ 2 ≥ 0 := by 
      apply sq_nonneg
    have h3 : (x - y) ^ 2 ≤ 1 := by 
      nlinarith [h1]
    have h4 : (x - y) ^ 2 = 0 ∨ (x - y) ^ 2 = 1 := by 
      have h5 : (x - y) ^ 2 ≤ 1 := h3
      have h6 : (x - y) ^ 2 ≥ 0 := h2
      have : (x - y) ^ 2 = 0 ∨ (x - y) ^ 2 = 1 := by
        have : (x - y) ^ 2 ≤ 1 := h5
        have : (x - y) ^ 2 ≥ 0 := h6
        interval_cases (x - y) ^ 2 <;> omega
      assumption
    rcases h4 with h4 | h4
    · -- Assume (x - y) ^ 2 = 0
      have h5 : x = y := by 
        nlinarith 
      have h6 : (x - 1) * (y - 1) = 1 := by 
        nlinarith [h1, h4, h5]
      have h7 : y = x := by 
        linarith [h5] 
      rw [h7] at h6 
      have h8 : (x - 1) ^ 2 = 1 := by 
        linarith 
      have h9 : x - 1 = 1 ∨ x - 1 = -1 := by 
        have h10 : (x - 1) ^ 2 = 1 := h8 
        rw [sq_eq_one_iff] at h10 
        tauto 
      rcases h9 with h9 | h9 
      · -- Assume x - 1 = 1 
        have hx : x = 2 := by 
          linarith 
        have hy : y = 2 := by 
          linarith [h5, hx] 
        simp [hx, hy] 
      · -- Assume x - 1 = -1 
        have hx : x = 0 := by 
          linarith 
        have hy : y = 0 := by 
          linarith [h5, hx] 
        simp [hx, hy] 
    · -- Assume (x - y) ^ 2 = 1 
      have h6 : (x - y) ^ 2 = 1 := by 
        linarith [h4] 
      have h5 : x - y = 1 ∨ x - y = -1 := by 
        have h6 : (x - y) ^ 2 = 1 := by 
          linarith [h4]
        have : x - y = 1 ∨ x - y = -1 := by 
          rw [sq_eq_one_iff] at h6 
          tauto 
        assumption 
      have h8 : (x - 1) * (y - 1) = 0 := by 
        nlinarith [h1, h6] 
      have h9 : x - 1 = 0 ∨ y - 1 = 0 := by 
        cases (mul_eq_zero.1 h8) with 
        | inl h11 => 
          left; linarith 
        | inr h22 => 
          right; linarith 
      rcases h9 with h9 | h9 
      · -- Assume x - 1 = 0 
        have hx1 : x = 1 := by 
          linarith 
        rcases h5 with h5 | h5 
        · -- Assume x - y = 1 
          have hy : y = 0 := by 
            nlinarith [h5, hx1] 
          norm_num [hx1, hy] 
        · -- Assume x - y = -1 
          have hy : y = 2 := by 
            nlinarith [h5, hx1] 
          norm_num [hx1, hy] 
      · -- Assume y - 1 = 0 
        have hy1 : y = 1 := by 
          linarith 
        rcases h5 with h5 | h5 
        · -- Assume x - y = 1 
          have hx1 : x = 2 := by 
            nlinarith [h5, hy1] 
          norm_num [hx1, hy1] 
        · -- Assume x - y = -1 
          have hx1 : x = 0 := by 
            nlinarith [h5, hy1] 
          norm_num [hx1, hy1] 
  · -- Show that each pair in the right side is a solution
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Verify (2, 1)
      norm_num 
    · -- Verify (1, 2)
      norm_num 
    · -- Verify (0, 0)
      norm_num 
    · -- Verify (2, 2)
      norm_num 
    · -- Verify (1, 0)
      norm_num 
    · -- Verify (0, 1)
      norm_num