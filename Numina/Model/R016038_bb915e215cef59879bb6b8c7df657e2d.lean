import Mathlib
open Polynomial

theorem algebra_2868 (a b c d : ℂ) (h : (2 * X ^ 2 - 7 * X + 1 : ℂ[X]).eval 1 = -4 ∧ (2 * X ^ 2 - 7 * X + 1 : ℂ[X]).eval 2 = -5 ∧ (2 * X ^ 2 - 7 * X + 1 : ℂ[X]).eval 4 = 5)
    (h' : (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℂ[X]).eval 5 = 4 ∧ (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℂ[X]).eval 1 = -4 ∧ (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℂ[X]).eval 2 = -5 ∧ (C a * X ^ 3 + C b * X ^ 2 + C c * X + C d : ℂ[X]).eval 4 = 5) :
    a - b + c - d = -40 := by
  rcases h' with ⟨h1, h2, h3, h4⟩
  simp [pow_succ, pow_zero, eval_add, eval_mul, eval_pow, eval_C] at h1 h2 h3 h4
  rcases h with ⟨h11, h22, h33⟩
  simp [pow_succ, pow_zero, eval_add, eval_mul, eval_pow, eval_C] at h11 h22 h33
  have h5 : a - b + c - d = -40 := by
    simp [sub_eq_add_neg] at *
    norm_num [Complex.ext_iff] at h1 h2 h3 h4 ⊢ 
    constructor <;> 
      ring_nf at h1 h2 h3 h4 ⊢ <;> 
        linarith
  exact_mod_cast h5