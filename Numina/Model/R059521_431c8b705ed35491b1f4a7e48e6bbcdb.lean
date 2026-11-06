import Mathlib

theorem calculus_155247 (f : ℝ → ℝ) (hf : f = fun x => x^2 - 3 * x + 5)
    (x : ℝ) (hx : x > 0) (h : deriv f x = 5 * deriv (fun x => x) x) :
    f x = 9 := by
  have f_def : f = fun x => x^2 - 3 * x + 5 := by
    exact hf
  have deriv_f : deriv f x = 2 * x - 3 := by 
    rw [f_def]
    simp [deriv_pow, deriv_sub, deriv_add, deriv_const, deriv_id', mul_comm]
    all_goals ring_nf <;> field_simp <;> ring
  have deriv_id : deriv (fun x : ℝ => x) x = 1 := by 
    simp [deriv_id']
  rw [deriv_f, deriv_id] at h
  have hx_eq : x = 4 := by 
    linarith
  rw [hx_eq]
  simp [f_def]
  all_goals norm_num