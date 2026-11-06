import Mathlib

theorem algebra_10265 {a b : ℝ} (hb : b = 6) :
  let var_inv_k (a b k : ℝ) : Prop := a * b = k;
  var_inv_k (a^2) (b^3) (7^2 * 3^3) → a^2 = 6.125 := by
  intro var_inv_k h
  rw [hb] at h
  norm_num at h 
  nlinarith