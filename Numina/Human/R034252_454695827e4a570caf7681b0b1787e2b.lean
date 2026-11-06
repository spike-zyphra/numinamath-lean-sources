import Mathlib

open Polynomial 

/- For how many integer values of $b$ does there exist a polynomial function with integer coefficients such that $f(2)=2010$ and $f(b)=8$ ?-/

theorem algebra_608607 {b : ℤ}: 
  (∃ (f : Polynomial ℤ), (f.eval 2 = 2010 ∧ f.eval b = 8) )↔ (b - 2) ∣ -2002 := by 
  constructor
  -- forward direction
  · intro h
    obtain ⟨f, ⟨h1, h2⟩⟩ := h
    rw [show -2002 = (8 : ℤ) - 2010 by norm_num]
    rw [← h1, ← h2]
    exact Polynomial.sub_dvd_eval_sub b 2 f
  -- backward direction
  · intro h
    let f : Polynomial ℤ := - ((2002 / (b - 2) : ℤ) : ℤ[X]) * (X -2) + (2010 : ℤ[X])
    use f
    constructor
    unfold f
    simp
    unfold f
    simp
    have eq_aux : 2002 / (b - 2) * (b - 2) = 2002 := by 
      have dvd_aux : b - 2 ∣ 2002 := by exact Int.dvd_neg.mp h
      exact Int.ediv_mul_cancel dvd_aux
    rw [eq_aux]
    norm_num

