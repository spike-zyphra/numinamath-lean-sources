import Mathlib

open Real

theorem calculus_228603 (f : ℝ → ℝ) (hf : f = log) :
    ∀ x > 0, deriv (deriv f) x < 0 := by
  intro x hx
  rw [hf]
  have h1 : deriv (deriv (fun (y : ℝ) => Real.log y)) x = -1 / (x ^ 2) := by 
    simp [deriv_log, deriv_div, deriv_const, deriv_id'', pow_two, div_eq_mul_inv]
    <;> field_simp [show x ≠ 0 by linarith] 
    <;> ring
  rw [h1]
  have h2 : -1 / (x ^ 2) < 0 := by 
    apply div_neg_of_neg_of_pos 
    norm_num 
    have h3 : x ^ 2 > 0 := by 
      nlinarith [sq_pos_of_pos hx] 
    linarith 
  linarith [h2]