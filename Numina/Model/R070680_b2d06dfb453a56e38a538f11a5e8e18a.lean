import Mathlib

open Real

theorem calculus_12377 {a : ℝ} (f : ℝ → ℝ) (hf : f = fun x => exp (x + a)) (g : ℝ → ℝ)
    (hg : g = fun x => x - 3) (x : ℝ) (hx : f x = g x) (h : deriv f x = 1) :
    a = -4 := by
  have eq1 : exp (x + a) = x - 3 := by
    rw [hf] at hx
    rw [hg] at hx
    simp at hx
    linarith
  have eq2 : deriv f x = exp (x + a) := by 
    rw [hf]
    simp [deriv_add_const, deriv_id'', add_assoc]
    all_goals try linarith
  rw [eq2] at h
  have h1 : x + a = 0 := by
    have h3 : exp (x + a) = 1 := by 
      linarith
    have h4 : x + a = 0 := by
      rw [exp_eq_one_iff] at h3
      linarith
    linarith
  have h5 : x = -a := by linarith
  rw [show x = -a by linarith] at eq1
  have h6 : exp ((-a : ℝ) + a) = 1 := by
    have h7 : (-a : ℝ) + a = (0 : ℝ) := by
      ring
    rw [h7]
    norm_num
  have h8 : (-a : ℝ) - 3 = (1 : ℝ) := by
    have h9 : exp ((-a : ℝ) + a) = (-a : ℝ) - 3 := by 
      linarith [eq1]
    linarith [h9, h6]
  linarith