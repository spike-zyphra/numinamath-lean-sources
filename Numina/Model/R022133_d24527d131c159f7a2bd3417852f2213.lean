import Mathlib

open Polynomial

theorem algebra_3107 {a b : ℝ} (h : (8 * X ^ 3 + C a * X ^ 2 + 7 * X - C 3) / (2 * X ^ 2 + C (-b) * X + C 1) = 4 * X - 5 ∧ (8 * X ^ 3 + C a * X ^ 2 + 7 * X - C 3) % (2 * X ^ 2 + C (-b) * X + C 1) = 2 * X + 2) : a = -10 - 4 / 5 := by
  have h1 := h.1 
  have h2 := h.2
  have eq1 : (8 * X ^ 3 + C a * X ^ 2 + 7 * X - C 3) =
      (2 * X ^ 2 + C (-b) * X + C 1) * (4 * X - 5) + (2 * X + 2) := by 
    rw [←h1, ←h2]
    apply Eq.symm 
    apply EuclideanDomain.div_add_mod 
  have eq12 := congr_arg (fun f => f.eval 1) eq1 
  simp [pow_two, pow_three] at eq12 
  have eq13 := congr_arg (fun f => f.eval 0) eq1 
  simp [pow_two, pow_three] at eq13 
  have eq14 := congr_arg (fun f => f.eval 2) eq1 
  simp [pow_two, pow_three] at eq14 
  ring_nf at eq12 eq13 eq14 
  have h5 : 5 * b = 1 := by
    linarith
  have hb : b = 1 / 5 := by
    linarith 
  have ha : a = - 54 / 5 := by 
    rw [hb] at eq12
    linarith 
  rw [ha]
  norm_num