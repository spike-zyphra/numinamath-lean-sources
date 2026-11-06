import Mathlib

theorem algebra_8148
    (a b : ℝ)
    (ha : 0 < a ∧ a < 1)
    (hb : -1 < b ∧ b < -a) :
    max (max (max (1 / a) (1 / (a - b))) (1 / (a + b))) (1 / (a ^ 2 - b ^ 2)) = 1 / a := by
  rcases ha with ⟨ha_pos, ha_lt_one⟩
  rcases hb with ⟨hb_gt_neg_one, hb_lt_neg_a⟩
  have h1 : 0 < a := ha_pos
  have h2 : a < 1 := ha_lt_one
  have h3 : -1 < b := hb_gt_neg_one
  have h4 : b < -a := hb_lt_neg_a
  have h5 : a - b > 0 := by
    linarith 
  have h6 : a + b < 0 := by 
    linarith 
  have h7 : a ^ 2 - b ^ 2 < 0 := by 
    have h8 : (a - b) * (a + b) < 0 := by 
      apply mul_neg_of_pos_of_neg 
      · linarith 
      · linarith 
    nlinarith 
  have h8 : 1 / a > 1 / (a - b) := by 
    apply (div_lt_div_iff (by linarith) (by linarith)).mpr
    nlinarith 
  have h9 : 1 / a > 1 / (a + b) := by
    have h10 : 1 / (a + b) < (0 : ℝ) := by 
      have h11 : a + b < 0 := h6 
      apply div_neg_of_pos_of_neg 
      · norm_num 
      · linarith 
    have h11 : 1 / a > (0 : ℝ) := by 
      positivity 
    linarith 
  have h10 : 1 / a > 1 / (a ^ 2 - b ^ 2) := by
    have h122 : 1 / (a ^ 2 - b ^ 2) < (0 : ℝ) := by 
      have h123 : a ^ 2 - b ^ 2 < 0 := h7 
      apply div_neg_of_pos_of_neg 
      · norm_num 
      · linarith 
    have h124 : 1 / a > (0 : ℝ) := by 
      positivity 
    linarith 
  have h11 : max (1 / a) (1 / (a - b)) = 1 / a := by 
    apply max_eq_left 
    linarith [h8]
  have h12 : max (max (1 / a) (1 / (a - b))) (1 / (a + b)) = 1 / a := by 
    rw [h11]
    apply max_eq_left 
    linarith [h9] 
  have h13 : max (max (max (1 / a) (1 / (a - b))) (1 / (a + b))) (1 / (a ^ 2 - b ^ 2)) = 1 / a := by 
    rw [h12]
    apply max_eq_left 
    linarith [h10] 
  exact h13