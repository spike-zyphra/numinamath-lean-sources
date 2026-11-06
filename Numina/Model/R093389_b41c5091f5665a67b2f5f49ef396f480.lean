import Mathlib

theorem algebra_225588 (x y : ℝ) (h₀ : 0 ≤ x + 1) (h₁ : 0 ≤ y - 1)
    (h₂ : Real.sqrt (x + 1) + Real.sqrt (y - 1) = 5) (h₃ : x + y = 13) :
    (x = 8 ∧ y = 5) ∨ (x = 3 ∧ y = 10) := by
  have h4 : y = 13 - x := by linarith
  rw [h4] at h₂
  have h5 : Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1) = 5 := h₂
  have h6 : Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1) = 5 := h5
  have h7 : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
  have h8 : Real.sqrt ((13 - x) - 1) ≥ 0 := Real.sqrt_nonneg ((13 - x) - 1)
  have h9 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt h₀
  have h10 : Real.sqrt ((13 - x) - 1) ^ 2 = (13 - x) - 1 := by
    have h9 : y - 1 ≥ 0 := h₁
    rw [show y - 1 = (13 - x) - 1 by linarith [h₃]] at h9
    apply Real.sq_sqrt
    nlinarith
  have h11 : Real.sqrt (x + 1) * Real.sqrt ((13 - x) - 1) = 6 := by
    have h6' : Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1) = 5 := h6
    have h12 : (Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1)) ^ 2 = 25 := by
      rw [h6']
      all_goals norm_num
    have h13 : (Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1)) ^ 2
      = Real.sqrt (x + 1) ^ 2 + Real.sqrt ((13 - x) - 1) ^ 2 + 2 * (Real.sqrt (x + 1) * Real.sqrt ((13 - x) - 1)) := by
        ring
    rw [h13] at h12
    have h14 : Real.sqrt (x + 1) ^ 2 + Real.sqrt ((13 - x) - 1) ^ 2 = 13 := by
      nlinarith [h9, h10, h₃]
    nlinarith [h14, h12]
  have h15 : Real.sqrt (x + 1) = 2 ∨ Real.sqrt (x + 1) = 3 := by
    have h16 : Real.sqrt (x + 1) + Real.sqrt ((13 - x) - 1) = 5 := h6
    have h17 : Real.sqrt (x + 1) * Real.sqrt ((13 - x) - 1) = 6 := h11
    have h18 : Real.sqrt (x + 1) ^ 2 - 5 * Real.sqrt (x + 1) + 6 = 0 := by 
      have h19 : Real.sqrt ((13 - x) - 1) = 5 - Real.sqrt (x + 1) := by linarith
      rw [h19] at h17
      nlinarith
    have h20 : (Real.sqrt (x + 1) - 2) * (Real.sqrt (x + 1) - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h20) with h21 h22
    · left
      linarith
    · right
      linarith
  cases h15 with
  | inl h23 =>
    have hx : x = 3 := by 
      have h24 : Real.sqrt (x + 1) = 2 := h23
      have h25 : x + 1 = (2 : ℝ) ^ 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] at h24
        · nlinarith
        all_goals nlinarith
      nlinarith
    have hy : y = 10 := by
      linarith [h₃, hx]
    right
    exact ⟨hx, hy⟩
  | inr h26 =>
    have hx : x = 8 := by 
      have h27 : Real.sqrt (x + 1) = 3 := h26
      have h28 : x + 1 = (3 : ℝ) ^ 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] at h27
        · nlinarith
        all_goals nlinarith
      nlinarith
    have hy : y = 5 := by
      linarith [h₃, hx]
    left
    exact ⟨hx, hy⟩