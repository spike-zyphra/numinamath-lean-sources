import Mathlib

  theorem inequalities_43462 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) (habc : a * b * c = 1) :
  3 ≤ a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - c) * (b - a)) +  c ^ 3 / ((c - a) * (c - b)) := by
    have h1 : a - b ≠ 0 := sub_ne_zero_of_ne hdist.1
    have h2 : a - c ≠ 0 := sub_ne_zero_of_ne hdist.2.1
    have h3 : b - c ≠ 0 := sub_ne_zero_of_ne hdist.2.2
    have h4 : b - a ≠ 0 := sub_ne_zero_of_ne (by tauto)
    have h5 : c - a ≠ 0 := sub_ne_zero_of_ne (by tauto)
    have h6 : c - b ≠ 0 := sub_ne_zero_of_ne (by tauto)

    have eq : a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - c) * (b - a)) +
          c ^ 3 / ((c - a) * (c - b)) = a + b + c := by
      field_simp [h1, h2, h3, h4, h5, h6]
      nlinarith [habc, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  
    rw [eq]
  
    nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
      mul_self_nonneg (a - b), mul_self_nonneg (a - c), mul_self_nonneg (b - c),
      mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, habc, 
      mul_pos (show 0 < a * b by nlinarith) (show 0 < c by nlinarith),
      mul_pos (show 0 < b * c by nlinarith) (show 0 < a by nlinarith),
      mul_pos (show 0 < a * c by nlinarith) (show 0 < b by nlinarith)]