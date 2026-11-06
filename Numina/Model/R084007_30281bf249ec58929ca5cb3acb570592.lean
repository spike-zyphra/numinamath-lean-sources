import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_283304 {a : ℝ} (f : ℝ → ℝ) (hf : f = λ x => exp (x + a))
  (h : ∃ x, deriv f x = 1 ∧ f x = x - 3) : a = -4 := by 
  rcases h with ⟨x, h1, h2⟩
  have h3 : deriv f x = exp (x + a) := by 
    rw [hf]
    simp [deriv_add, deriv_id'', add_assoc, deriv_const, mul_one]
    all_goals linarith
  rw [h3] at h1
  have h4 : exp (x + a) = 1 := by
    linarith
  have h5 : f x = exp (x + a) := by
    rw [hf]
    all_goals linarith
  rw [h5] at h2
  have h6 : x - 3 = 1 := by
    linarith [h4, h2]
  have hx : x = 4 := by
    linarith
  rw [hx] at h4
  have h7 : 4 + a = 0 := by
    have h8 : exp (4 + a) = 1 := by
      have : 4 + a = (4 + a : ℝ) := by rfl
      rw [show 4 + a = (4 + a : ℝ) by rfl] at h4
      linarith [h4]
      all_goals norm_num at h4 ⊢ <;> try linarith
    have h9 : 4 + a = (0 : ℝ) := by
      rw [exp_eq_one_iff] at h8 
      all_goals linarith [h8]
      all_goals try linarith
    linarith [h9]
  linarith