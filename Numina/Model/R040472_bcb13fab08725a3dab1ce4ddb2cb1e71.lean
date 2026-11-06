import Mathlib

theorem algebra_219698 (x : ℝ) (hx : x ≠ 6) (hs : (11 * x - 6) / (6 - x) ≥ 0) :
    (x^2 + 1) / (x^2 + 11) = (1 / 6) * Real.sqrt ((11 * x - 6) / (6 - x)) ↔
    x = 1 ∨ x = 2 ∨ x = 3 := by
  constructor
  · -- Forward direction: if the equation holds, then x ∈ {1, 2, 3}
    intro h_eq
    have h1 : 0 ≤ (11 * x - 6) / (6 - x) := by linarith 
    have h2 : Real.sqrt ((11 * x - 6) / (6 - x)) ≥ 0 := by positivity 
    have h3 : (Real.sqrt ((11 * x - 6) / (6 - x))) ^ 2 = (11 * x - 6) / (6 - x) := by 
      rw [Real.sq_sqrt]
      linarith
    have h4 : 6 - x ≠ 0 := by
      intro h
      apply hx
      linarith
    have h5 : Real.sqrt ((11 * x - 6) / (6 - x)) = 6 * (x^2 + 1) / (x^2 + 11) := by
      field_simp at h_eq ⊢
      nlinarith [Real.sqrt_nonneg ((11 * x - 6) / (6 - x)), h2, sq_nonneg (Real.sqrt ((11 * x - 6) / (6 - x)) - 6 * (x^2 + 1) / (x^2 + 11)), sq_nonneg (x^2 + 1), sq_nonneg (x^2 + 11), sq_nonneg (6 - x), sq_nonneg (11 * x - 6)]
    have h8 : 0 ≤ 6 - x := by
      by_contra h
      push_neg at h
      have h9 : (11 * x - 6) / (6 - x) < 0 := by
        apply div_neg_of_pos_of_neg
        linarith
        linarith
      linarith [show (11 * x - 6) / (6 - x) ≥ 0 by linarith]
    have h9 : (6 - x) ≥ 0 := by linarith 
    have heq2 : (Real.sqrt ((11 * x - 6) / (6 - x))) ^2 = (6 * (x^2 + 1) / (x^2 + 11)) ^2 := by
      rw [h5]
    rw [h3] at heq2
    have h10 : x^2 + 11 > 0 := by nlinarith
    have h12 : (11 * x - 6) * (x^2 + 11)^2 = 36 * (6 - x) * (x^2 + 1)^2 := by
      have h13 : 0 < (6 - x) := by 
        by_contra h
        push_neg at h
        have h14 : (6 - x) = 0 := by nlinarith
        have h15 : x = 6 := by linarith 
        contradiction 
      have h14 : (6 - x) > 0 := h13
      field_simp [(show 6 - x ≠ 0 by intro h'; apply hx; linarith ), (show x^2 + 11 ≠ 0 by nlinarith)] at heq2 ⊢
      <;> nlinarith [sq_nonneg (x^2 + 1), sq_nonneg (x^2 + 11), sq_nonneg (6 - x), sq_nonneg (11 * x - 6)]
    have h13 : (x - 1) * (x - 2) * (x - 3) = 0 := by
      nlinarith [sq_nonneg (x^2 + 1), sq_nonneg (x^2 + 11), sq_nonneg (6 - x), sq_nonneg (11 * x - 6)]
    cases' (mul_eq_zero.mp h13) with h14 h15
    cases' (mul_eq_zero.mp h14) with h16 h17
    · -- x - 1 = 0
      left
      linarith 
    · -- x - 2 = 0
      right
      left 
      linarith 
    · -- x - 3 = 0
      right 
      right 
      linarith 
  · -- Backward direction: if x ∈ {1, 2, 3}, then equation holds
    rintro (h | h | h)
    · -- x = 1
      rw [h]
      have h1 : Real.sqrt ((11 * (1 : ℝ) - 6) / (6 - (1 : ℝ))) = Real.sqrt (5 / 5) := by norm_num 
      rw [h1]
      have h2 : Real.sqrt ((5 / (5 : ℝ))) = 1 := by
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h2]
      norm_num 
    · -- x = 2
      rw [h]
      have h1 : Real.sqrt ((11 * (2 : ℝ) - 6) / (6 - (2 : ℝ))) = Real.sqrt (16 / 4) := by norm_num
      rw [h1]
      have h2 : Real.sqrt ((16 / (4 : ℝ))) = 2 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h2]
      norm_num 
    · -- x = 3
      rw [h]
      have h1 : Real.sqrt ((11 * (3 : ℝ) - 6) / (6 - (3 : ℝ))) = Real.sqrt (27 / 3) := by norm_num
      rw [h1]
      have h2 : Real.sqrt ((27 / (3 : ℝ))) = 3 := by 
        rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      rw [h2]
      norm_num