import Mathlib

theorem algebra_2168 (x y z : ℝ) (hx : abs x ≤ 3) (hy : abs y ≤ 1) (hz : abs z ≤ 4)
(h : abs (x - 2 * y + z) = 9) : x ^ 2 * y ^ 2011 * z ^ 3 = -576 := by
  have h1 : -3 ≤ x := by 
    linarith [abs_le.mp hx]
  have h2 : x ≤ 3 := by 
    linarith [abs_le.mp hx]
  have h3 : -1 ≤ y := by 
    linarith [abs_le.mp hy]
  have h4 : y ≤ 1 := by 
    linarith [abs_le.mp hy]
  have h5 : -4 ≤ z := by 
    linarith [abs_le.mp hz]
  have h6 : z ≤ 4 := by 
    linarith [abs_le.mp hz]
  cases eq_or_eq_neg_of_abs_eq h with
  | inl h_eq =>
    have hx_eq : x = 3 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    have hy_eq : y = -1 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    have hz_eq : z = 4 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    rw [hx_eq, hy_eq, hz_eq]
    norm_num
  | inr h_eq =>
    have hx_eq : x = -3 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    have hy_eq : y = 1 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    have hz_eq : z = -4 := by
      linarith [h_eq, h1, h2, h3, h4, h5, h6]
    rw [hx_eq, hy_eq, hz_eq]
    norm_num