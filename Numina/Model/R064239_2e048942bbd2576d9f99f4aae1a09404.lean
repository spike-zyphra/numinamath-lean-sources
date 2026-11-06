import Mathlib

open Real

theorem calculus_319779 {a : ℝ} (ha : ∃ x, exp (x + a) = x - 3 ∧ deriv (fun x => exp (x + a)) x = 1) :
    a = -4 := by 
  rcases ha with ⟨x, h1, h2⟩
  have h_deriv : deriv (fun x => exp (x + a)) x = exp (x + a) := by
    simp [deriv_const, deriv_id', add_assoc]
    all_goals try ring_nf <;> try simp [exp_add]
    all_goals try norm_num
  rw [h_deriv] at h2
  have h_eq1 : x + a = (0 : ℝ) := by 
    have h : exp (x + a) = 1 := h2
    have : x + a = 0 := by
      rw [exp_eq_one_iff] at h
      linarith [h]
      all_goals linarith [h]
    linarith
  have hx_eq_neg_a : x = -a := by linarith 
  rw [show x = -a by linarith] at h1 
  have h_eq2 : exp ( (-a) + a ) = (-a : ℝ) - 3 := by linarith [h1]
  have h_eq3 : exp ( (-a) + a ) = 1 := by 
    have h2_simp : (-a) + a = (0 : ℝ) := by ring
    rw [h2_simp]
    norm_num [exp_zero]
  rw [h_eq3] at h_eq2 
  linarith