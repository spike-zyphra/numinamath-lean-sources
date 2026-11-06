import Mathlib 

theorem algebra_165006 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
    (hab : a < b) (hcb : c < b)
    (h : a + c - b > 0) : 
    ∃ s : ℝ, s = Real.sqrt (a * b * c / (a + c - b)) ∧ s > a ∧ s > b ∧ s > c := by
  use Real.sqrt (a * b * c / (a + c - b))
  constructor
  · -- Show s = Real.sqrt (a * b * c / (a + c - b))
    rfl
  constructor
  · -- Show s > a
    have h1 : a * b * c / (a + c - b) > 0 := by apply div_pos; positivity; linarith
    have h2 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 > a ^ 2 := by
      have h6 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 = a * b * c / (a + c - b) := by
        rw [Real.sq_sqrt]
        positivity
      rw [h6]
      have h4 : a * (a + c - b) < b * c := by
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
      have h5 : a * b * c / (a + c - b) > a ^ 2 := by
        have h8 : a + c - b > 0 := by linarith
        have h9 : a * b * c > a ^ 2 * (a + c - b) := by
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
        have h10 : a * b * c / (a + c - b) > a ^ 2 := by
          apply (lt_div_iff₀' (by linarith)).mpr
          nlinarith
        linarith
      linarith
    have h3 : Real.sqrt (a * b * c / (a + c - b)) > a := by
      have h4 : Real.sqrt (a * b * c / (a + c - b)) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      nlinarith [Real.sqrt_nonneg (a * b * c / (a + c - b)), Real.sq_sqrt (show 0 ≤ a * b * c / (a + c - b) by positivity)]
    linarith
  constructor
  · -- Show s > b
    have h1 : a * b * c / (a + c - b) > 0 := by apply div_pos; positivity; linarith
    have h2 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 > b ^ 2 := by
      have h6 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 = a * b * c / (a + c - b) := by
        rw [Real.sq_sqrt]
        positivity
      rw [h6]
      have h4 : b * (a + c - b) < a * c := by
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
      have h5 : a * b * c / (a + c - b) > b ^ 2 := by
        have h8 : a + c - b > 0 := by linarith
        have h9 : a * b * c > b ^ 2 * (a + c - b) := by
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
        have h10 : a * b * c / (a + c - b) > b ^ 2 := by
          apply (lt_div_iff₀' (by linarith)).mpr
          nlinarith
        linarith
      linarith
    have h3 : Real.sqrt (a * b * c / (a + c - b)) > b := by
      have h4 : Real.sqrt (a * b * c / (a + c - b)) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      nlinarith [Real.sqrt_nonneg (a * b * c / (a + c - b)), Real.sq_sqrt (show 0 ≤ a * b * c / (a + c - b) by positivity)]
    linarith
  · -- Show s > c
    have h1 : a * b * c / (a + c - b) > 0 := by apply div_pos; positivity; linarith
    have h2 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 > c ^ 2 := by
      have h6 : (Real.sqrt (a * b * c / (a + c - b))) ^ 2 = a * b * c / (a + c - b) := by
        rw [Real.sq_sqrt]
        positivity
      rw [h6]
      have h4 : c * (a + c - b) < a * b := by
        nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
      have h5 : a * b * c / (a + c - b) > c ^ 2 := by
        have h8 : a + c - b > 0 := by linarith
        have h9 : a * b * c > c ^ 2 * (a + c - b) := by
          nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (b - a), sq_nonneg (b - c), sq_nonneg (a - c)]
        have h10 : a * b * c / (a + c - b) > c ^ 2 := by
          apply (lt_div_iff₀' (by linarith)).mpr
          nlinarith
        linarith
      linarith
    have h3 : Real.sqrt (a * b * c / (a + c - b)) > c := by
      have h4 : Real.sqrt (a * b * c / (a + c - b)) > 0 := by
        apply Real.sqrt_pos.mpr
        positivity
      nlinarith [Real.sqrt_nonneg (a * b * c / (a + c - b)), Real.sq_sqrt (show 0 ≤ a * b * c / (a + c - b) by positivity)]
    linarith