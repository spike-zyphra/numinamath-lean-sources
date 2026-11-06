import Mathlib

theorem inequalities_129032 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    1 / (a ^ 3 + b * c) + 1 / (b ^ 3 + c * a) + 1 / (c ^ 3 + a * b) ≤
    ((a * b + b * c + c * a) ^ 2) / 6 := by 
  have h1 : 1 / (a ^ 3 + b * c) = a / (a^4 + 1) := by
    have h2 : a ^ 3 + b * c = (a^4 + 1) / a := by
      have h3 : b * c = 1 / a := by
        field_simp
        nlinarith
      field_simp at h3 ⊢
      <;> nlinarith
    rw [h2]
    field_simp
    <;> nlinarith 
  have h4 : 1 / (b ^ 3 + c * a) = b / (b^4 + 1) := by 
    have h5 : b ^ 3 + c * a = (b^4 + 1) / b := by 
      have h6 : c * a = 1 / b := by
        field_simp
        nlinarith 
      field_simp at h6 ⊢
      <;> nlinarith 
    rw [h5]
    field_simp
    <;> nlinarith 
  have h7 : 1 / (c ^ 3 + a * b) = c / (c^4 + 1) := by 
    have h8 : c ^ 3 + a * b = (c^4 + 1) / c := by 
      have h9 : a * b = 1 / c := by 
        field_simp 
        nlinarith 
      field_simp at h9 ⊢ 
      <;> nlinarith 
    rw [h8]
    field_simp
    <;> nlinarith 
  rw [h1, h4, h7]
  have h8 : a / (a^4 + 1) ≤ 1 / (2 * a) := by 
    have h9 : 0 < a ^ 4 + 1 := by positivity 
    have h10 : 0 < 2 * a := by positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (a ^ 2 - 1)]
  have h9 : b / (b ^ 4 + 1) ≤ 1 / (2 * b) := by 
    have h9 : 0 < b ^ 4 + 1 := by positivity 
    have h10 : 0 < 2 * b := by positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (b ^ 2 - 1)]
  have h10 : c / (c ^ 4 + 1) ≤ 1 / (2 * c) := by 
    have h11 : 0 < c ^ 4 + 1 := by positivity 
    have h12 : 0 < 2 * c := by positivity 
    apply (div_le_div_iff (by positivity) (by positivity)).mpr 
    nlinarith [sq_nonneg (c ^ 2 - 1)]
  -- Summing the individual inequalities 
  have h11 : a / (a^4 + 1) + b / (b^4 + 1) + c / (c^4 + 1) ≤ 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) := by 
    linarith [h8, h9, h10]
  have h12 : 1 / (2 * a) + 1 / (2 * b) + 1 / (2 * c) = (a * b + b * c + c * a) / 2 := by
    have h13 : a * b * c = 1 := habc 
    field_simp 
    nlinarith [h13, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  -- The following lemma is needed to establish the final result 
  have h14 : (a * b + b * c + c * a) / 2 ≤ ((a * b + b * c + c * a) ^ 2) / 6 := by
    have h16 : (a * b + b * c + c * a) ≥ 3 := by
      nlinarith [sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, habc
      ]
    -- Proving the inequality by showing that the difference is non-negative.
    have h17 : ((a * b + b * c + c * a) ^ 2) / 6 - (a * b + b * c + c * a) / 2 ≥ 0 := by 
      have h18 : (a * b + b * c + c * a) ^ 2 / 6 - (a * b + b * c + c * a) / 2 = ((a * b + b * c + c * a) ^ 2 - 3 * (a * b + b * c + c * a)) / 6 := by
        ring_nf 
      rw [h18]
      have h19 : (a * b + b * c + c * a) ^ 2 - 3 * (a * b + b * c + c * a) ≥ 0 := by
        nlinarith [h16]
      apply div_nonneg
      · linarith
      · norm_num 
    linarith [h17]
  linarith [h11, h12, h14]
  all_goals positivity