import Mathlib

theorem algebra_254509 (x1 x2 y1 y2 : ℝ) (hx1 : 6*x1^2-5*x1+1=0) (hx2 : 6*x2^2-5*x2+1=0)
    (hy1 : y1=(x1+1)/(x1-1)) (hy2 : y2=(x2+1)/(x2-1)) :
    y1^2+5*y1+6=0 ∧ y2^2+5*y2+6=0 := by 
  have h1factored : (x1 - 1/2) * (x1 - 1/3) = 0 := by 
    linarith 
  have h2factored : (x2 - 1/2) * (x2 - 1/3) = 0 := by 
    linarith
  have hx1_eq : x1 = 1/2 ∨ x1 = 1/3 := by 
    cases (mul_eq_zero.mp h1factored) with 
    | inl h11 => 
      left 
      linarith 
    | inr h12 => 
      right 
      linarith 
  have hx2_eq : x2 = 1/2 ∨ x2 = 1/3 := by 
    cases (mul_eq_zero.mp h2factored) with 
    | inl h21 => 
      left 
      linarith 
    | inr h22 => 
      right 
      linarith 
  cases hx1_eq with
  | inl h12 =>
    -- x1 = 1/2
    have hx1_val : x1 = 1/2 := h12
    cases hx2_eq with
    | inl h22 =>
      -- x2 = 1/2 
      have hx2_val : x2 = 1/2 := h22
      have hy1_val : y1 = -3 := by
        rw [hy1, hx1_val]
        norm_num
      have hy2_val : y2 = -3 := by
        rw [hy2, hx2_val]
        norm_num 
      constructor 
      · -- Show y1 satisfies
        rw [hy1_val]
        norm_num
      · -- Show y2 satisfies 
        rw [hy2_val]
        norm_num
    | inr h23 =>
      -- x2 = 1/3 
      have hx2_val : x2 = 1/3 := h23
      have hy1_val : y1 = -3 := by
        rw [hy1, hx1_val]
        norm_num 
      have hy2_val : y2 = -2 := by 
        rw [hy2, hx2_val]
        norm_num 
      constructor 
      · -- Show y1 satisfies 
        rw [hy1_val]
        norm_num 
      · -- Show y2 satisfies 
        rw [hy2_val]
        norm_num 
  | inr h13 =>
    -- x1 = 1/3 
    have hx1_val : x1 = 1/3 := h13
    cases hx2_eq with 
    | inl h22 => 
      -- x2 = 1/2 
      have hx2_val : x2 = 1/2 := h22
      have hy1_val : y1 = -2 := by 
        rw [hy1, hx1_val]
        norm_num 
      have hy2_val : y2 = -3 := by 
        rw [hy2, hx2_val]
        norm_num 
      constructor 
      · -- Show y1 satisfies 
        rw [hy1_val]
        norm_num 
      · -- Show y2 satisfies 
        rw [hy2_val]
        norm_num 
    | inr h23 => 
      -- x2 = 1/3 
      have hx2_val : x2 = 1/3 := h23
      have hy1_val : y1 = -2 := by 
        rw [hy1, hx1_val]
        norm_num 
      have hy2_val : y2 = -2 := by 
        rw [hy2, hx2_val]
        norm_num 
      constructor 
      · -- Show y1 satisfies 
        rw [hy1_val]
        norm_num 
      · -- Show y2 satisfies 
        rw [hy2_val]
        norm_num