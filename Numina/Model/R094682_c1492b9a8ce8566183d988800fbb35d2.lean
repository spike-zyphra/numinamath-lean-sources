import Mathlib

theorem algebra_62791 {P Q : ℝ → ℝ}
    (hP : P = fun x => x^3 - 2 * x + 1)
    (hQ : Q = fun x => x^3 - 4 * x^2 + 4 * x - 1)
    (r : ℝ) (hr : P r = 0) : Q (r^2) = 0 := by 
  have hr_eq : r^3 - 2 * r + 1 = 0 := by 
    rw [hP] at hr 
    simp at hr 
    linarith
  have h_eq : r^3 = 2 * r - 1 := by linarith [hr_eq]
  have h_eq_r4 : r^4 = 2 * r^2 - r := by
    calc 
      r^4 = r * r^3 := by ring
      _ = r * (2 * r - 1) := by rw [h_eq]
      _ = 2 * r^2 - r := by ring 
  have h_eq_r5 : r^5 = 4 * r - 2 - r^2 := by 
    calc 
      r^5 = r * r^4 := by ring 
      _ = r * (2 * r^2 - r) := by rw [h_eq_r4]
      _ = 2 * r^3 - r^2 := by ring 
      _ = 2 * (2 * r - 1) - r^2 := by rw [h_eq]
      _ = 4 * r - 2 - r^2 := by ring 
  have h_eq_r6 : r^6 = 4 * r^2 - 4 * r + 1 := by 
    calc 
      r^6 = r * r^5 := by ring 
      _ = r * (4 * r - 2 - r^2) := by rw [h_eq_r5]
      _ = 4 * r^2 - 2 * r - r^3 := by ring 
      _ = 4 * r^2 - 2 * r - (2 * r - 1) := by rw [h_eq]
      _ = 4 * r^2 - 4 * r + 1 := by ring 
  rw [hQ] 
  simp 
  -- Compute Q(r^2) by substituting r^6, r^4 
  -- r^6 = 4r^2 - 4r + 1 
  -- r^4 = 2r^2 - r 
  -- compute r^6 -4r^4 +4r^2 -1 
  -- (4r^2 -4r +1) -4*(2r^2 - r) +4r^2 -1 =0
  nlinarith [sq_nonneg (r^2 - 1), sq_nonneg (r - 1), sq_nonneg (r - 2), sq_nonneg (r^2), sq_nonneg (r^2 - r), sq_nonneg (r * r * r * (r - 1)), h_eq, hr_eq]
  all_goals nlinarith
  all_goals ring_nf <;> nlinarith
  all_goals nlinarith
  <;> nlinarith
  <;> ring_nf <;> nlinarith
  <;> nlinarith
  all_goals nlinarith
  <;> norm_num <;> linarith 
  all_goals nlinarith
  <;> nlinarith
  all_goals nlinarith
  <;> norm_num
  all_goals nlinarith
  <;> norm_num
  <;> ring_nf <;> norm_num
  <;> norm_num
  all_goals nlinarith