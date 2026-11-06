import Mathlib
open Polynomial

theorem algebra_8933 {a b c d : ℝ} (f : ℝ → ℝ) (hf : f = fun x => a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP : f 1 = 0 ∧ deriv f 1 = 0) (hQ : f 2 = 2 ∧ deriv f 2 = 0) :
    a = -4 ∧ b = 18 ∧ c = -24 ∧ d = 10 := by
  have eq1 : f 1 = 0 := hP.1
  simp [hf] at eq1

  have eq3 : f 2 = 2 := hQ.1
  simp [hf] at eq3
  
  have eq2 : deriv f 1 = 0 := hP.2
  have eq4 : deriv f 2 = 0 := hQ.2
  
  have deriv_eq : deriv f = fun x => 3 * a * x ^ 2 + 2 * b * x + c := by
    funext x
    rw [hf]
    simp [deriv_pow, deriv_add, deriv_mul, deriv_id', mul_comm c, mul_assoc]
    field_simp
    ring
  
  have eq2' : deriv f 1 = 0 := eq2
  rw [deriv_eq] at eq2'
  simp at eq2'

  have eq4' : deriv f 2 = 0 := eq4
  rw [deriv_eq] at eq4'
  simp at eq4'

  have ha : a = -4 := by
    linarith [eq1, eq3, eq2', eq4']
  
  have hb : b = 18 := by
    linarith [eq1, ha, eq3, eq2', eq4']
  
  have hc : c = -24 := by
    linarith [eq1, ha, hb, eq3, eq2', eq4']

  have hd : d = 10 := by
    linarith [eq1, ha, hb, hc]

  exact ⟨ha, hb, hc, hd⟩