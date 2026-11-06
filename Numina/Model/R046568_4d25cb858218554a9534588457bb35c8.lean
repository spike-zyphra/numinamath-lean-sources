import Mathlib
open Real

theorem algebra_160621 : {(x, y) : ℝ × ℝ | x ^ 4 + y ^ 4 = 12 * (x ^ 2 + y ^ 2) - 6 * x ^ 2 * y ^ 2 + 16 ∧ x * y = 3} = {(-1, -3), (3, 1), (-3, -1), (1, 3)}:= by
  ext ⟨x, y⟩
  simp
  constructor
  · -- Assume (x, y) satisfies both equations, prove (x,y) ∈ { ... }
    intro h
    rcases h with ⟨h1, h2⟩
    have h_eq : (x ^ 2 + y ^ 2 - 2) * (x ^ 2 + y ^ 2 - 10) = 0 := by
      have h1' : x ^ 4 + y ^ 4 = (x^2 + y^2)^2 - 2 * (x * y) ^ 2 := by ring
      rw [h1'] at h1
      nlinarith
    have h_cases : (x ^ 2 + y ^ 2 - 2 = 0) ∨ (x ^ 2 + y ^ 2 - 10 = 0) := by
      cases mul_eq_zero.mp h_eq with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        linarith
    cases h_cases with
    | inl hq_2 => -- x ^ 2 + y ^ 2 = 2
      have h_4 : (x - y) ^ 2 = -4 := by
        have h3 : x^2 + y^2 = 2 := by linarith
        nlinarith
      exfalso
      have h_24 : (x - y) ^ 2 ≥ 0 := by apply sq_nonneg
      nlinarith
    | inr hq_10 => -- x ^2 + y^2 =10
      have hq_eq_10 : x ^2 + y ^2 = 10 := by linarith
      have h12 : (x + y) ^ 2 = 16 := by
        have h11 : x * y = 3 := h2
        nlinarith
      have h15 : x + y = 4 ∨ x + y = -4 := by
        have h : (x + y) ^2 - 16 = 0 := by nlinarith
        have : (x + y - 4) * (x + y + 4) = 0 := by nlinarith
        cases' mul_eq_zero.mp this with h24 h42
        · left
          linarith
        · right
          linarith
      cases h15 with
      | inl h15an4 =>
        -- x + y =4
        have h16 : (x - y) ^2 = 4 := by
          have h17 : x + y = 4 := h15an4
          nlinarith
        have h17 : x - y = 2 ∨ x - y = -2 := by
          have h : (x - y) ^2 - 4 = 0 := by nlinarith
          have : (x - y - 2) * (x - y + 2) = 0 := by nlinarith
          cases' mul_eq_zero.mp this with h211 h321
          · left
            linarith
          · right
            linarith
        cases h17 with
        | inl h172 =>
          have hx11 : x = 3 := by
            have h18x : x + y = 4 := h15an4
            have h12y2 : y = x - 2 := by linarith
            rw [h12y2] at h2
            nlinarith
          have hy11 : y = 1 := by
            rw [hx11] at h2
            nlinarith
          simp [hx11, hy11]
        | inr h17n2 =>
          have hx12 : x = 1 := by
            have h18x : x + y = 4 := h15an4
            have h12y2 : y = x - (-2) := by linarith
            rw [h12y2] at h2
            nlinarith
          have hy12 : y = 3 := by
            rw [hx12] at h2
            nlinarith
          simp [hx12, hy12]
      | inr h15n4 =>
        -- x + y =-4
        have h16 : (x - y) ^2 = 4 := by
          have h17 : x + y = -4 := h15n4
          nlinarith
        have h17 : x - y = 2 ∨ x - y = -2 := by
          have h : (x - y) ^2 - 4 = 0 := by nlinarith
          have : (x - y - 2) * (x - y + 2) = 0 := by nlinarith
          cases' mul_eq_zero.mp this with h24 h42
          · left
            linarith
          · right
            linarith
        cases h17 with
        | inl h172 =>
          have hx21 : x = -1 := by
            have h118 : x + y = -4 := h15n4
            have h119 : y = x - 2 := by linarith
            rw [h119] at h2
            nlinarith
          have hy21 : y = -3 := by
            rw [hx21] at h2
            nlinarith
          simp [hx21, hy21]
        | inr h17n2 =>
          have hx22 : x = -3 := by
            have h118 : x + y = -4 := h15n4
            have h119 : y = x - (-2) := by linarith
            rw [h119] at h2
            nlinarith
          have hy22 : y = -1 := by
            rw [hx22] at h2
            nlinarith
          simp [hx22, hy22]
  · rintro (h | h | h | h)
    · norm_num [h.1, h.2]
    · norm_num [h.1, h.2]
    · norm_num [h.1, h.2]
    · norm_num [h.1, h.2]