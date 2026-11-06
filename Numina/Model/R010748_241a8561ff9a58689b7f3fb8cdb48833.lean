import Mathlib

theorem algebra_13412 (f : ℝ → ℝ) (hf : 2 * f = λx ↦ -3 * x + 6) :
    deriv f 1 = -3 / 2 := by 
  have h1 : f = λ x ↦ (-3 / 2) * x + 3 := by 
    funext x 
    have eq1 : 2 * f x = -3 * x + 6 := by 
      simpa using congr_fun hf x
    have eq2 : f x = (-3 / 2) * x + 3 := by 
      linarith 
    simpa using eq2 
  rw [h1]
  simp [deriv_add, deriv_mul, deriv_id'', mul_comm]
  all_goals norm_num 
  <;> try { norm_num } <;> try { ring } <;> try { ring_nf <;> norm_num } <;> try { norm_num }