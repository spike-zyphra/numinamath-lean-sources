import Mathlib

open Polynomial

theorem algebra_3510 {f : ℝ → ℝ} (hf0 : f = fun x => a * x^3 + b * x^2 + c * x + d)
    (h1 : f (-1) = -1) (h2 : f 0 = 3) (h3 : f 1 = 13) (h4 : f 2 = 35) :
    f = fun x => x^3 + 3 * x^2 + 6 * x + 3 := by

  -- Substituting given points into the polynomial
  have eqn1 : a * (-1)^3 + b * (-1)^2 + c * (-1) + d = -1 := by
    rw [hf0] at h1 
    simpa using h1

  have eqn2 : a * 0^3 + b * 0^2 + c * 0 + d = 3 := by
    rw [hf0] at h2 
    simpa using h2

  have eqn3 : a * 1^3 + b * 1^2 + c * 1 + d = 13 := by 
    rw [hf0] at h3 
    simpa using h3

  have eqn4 : a * 2^3 + b * 2^2 + c * 2 + d = 35 := by 
    rw [hf0] at h4 
    simpa using h4
  
  -- Solving the system of equations
  have hd : d = 3 := by linarith

  have eqn1' : -a + b - c = -4 := by
    linarith [eqn1, hd]

  have eqn3' : a + b + c = 10 := by
    linarith [eqn3, hd]

  have eqn4' : 8 * a + 4 * b + 2 * c = 32 := by
    linarith [eqn4, hd]

  -- Now we're down to three variables
  have hb : b = 3 := by 
    have : 2 * b = 6 := by linarith [eqn1', eqn3']
    linarith

  -- Now solve for a and c
  have h1 : a + c = 7 := by 
    linarith [eqn3', hb]

  -- Solving the final equations
  have ha : a = 1 := by 
    have h2' : 8 * a + 4 * 3 + 2 * c = 32 := by linarith [hb, eqn4']
    nlinarith [h1, h2']

  have hc : c = 6 := by 
    linarith [h1, ha]

  -- Now we can prove that f is the given polynomial
  ext x
  simp [hf0, ha, hb, hc, hd]
  <;> ring