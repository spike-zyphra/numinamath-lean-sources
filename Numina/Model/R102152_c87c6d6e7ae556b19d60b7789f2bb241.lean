import Mathlib

theorem algebra_226731 :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ x y : ℝ, MvPolynomial.eval (fun n => if n = 0 then x else y) f ≠ 0 ∧
    ∀ ε > 0, ∃ x y : ℝ, MvPolynomial.eval (fun n => if n = 0 then x else y) f ∈ Set.Ioo (-ε) ε := by
  use (MvPolynomial.C (1 : ℝ) * (MvPolynomial.X (0 : Fin 2)) ^ 2 + 
     (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1) ^ 2)
  intro x y
  constructor
  · -- Show $f(x, y) ≠ 0$ for all $x, y$.
    by_contra h
    have eq : MvPolynomial.eval (fun n => if n = 0 then x else y) 
         (MvPolynomial.C (1 : ℝ) * (MvPolynomial.X (0 : Fin 2)) ^ 2 + (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1) ^ 2) = 0 := by 
        simpa using h
    have eq1 : x^2 + (x * y - 1)^2 = 0 := by 
      simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_X] at eq 
      <;> ring_nf at eq ⊢ <;> linarith
    have h1 : x^2 = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (x * y - 1)]
    have h2 : (x * y - 1)^2 = 0 := by nlinarith [sq_nonneg (x), sq_nonneg (x * y - 1)]
    have hx : x = 0 := by 
      nlinarith
    have h3 : x * y - 1 = 0 := by 
      nlinarith
    rw [hx] at h3
    nlinarith
  · -- Show that $f(x, y)$ can be arbitrarily close to zero
    intro ε hε
    use Real.sqrt (ε / 2)
    use (1 + Real.sqrt (ε / 2) / 2) / Real.sqrt (ε / 2)
    have h1 : Real.sqrt (ε / 2) ≥ 0 := by positivity
    have h2 : Real.sqrt (ε / 2) ^ 2 = ε / 2 := by
      rw [Real.sq_sqrt]
      linarith
      all_goals linarith
    have h3 : MvPolynomial.eval (fun n => if n = 0 then Real.sqrt (ε / 2) else (1 + Real.sqrt (ε / 2) / 2) / Real.sqrt (ε / 2) ) 
        (MvPolynomial.C (1 : ℝ) * (MvPolynomial.X (0 : Fin 2)) ^ 2 + (MvPolynomial.X (0 : Fin 2) * MvPolynomial.X (1 : Fin 2) - 1) ^ 2) =
        Real.sqrt (ε / 2) ^ 2 + (Real.sqrt (ε / 2) * ((1 + Real.sqrt (ε / 2) / 2) / Real.sqrt (ε / 2)) - 1) ^ 2 := by
      simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]
      <;> ring_nf <;> simp [Fin.sum_univ_two]
      <;> ring
    rw [h3]
    have h4 : Real.sqrt (ε / 2) ^ 2 = ε / 2 := by
      rw [Real.sq_sqrt]
      linarith
      all_goals linarith
    have h5 : Real.sqrt (ε / 2) * ((1 + Real.sqrt (ε / 2) / 2) / Real.sqrt (ε / 2)) - 1 = Real.sqrt (ε / 2) / 2 := by
      field_simp [ne_of_gt (show Real.sqrt (ε / 2) > 0 by positivity)]
      <;> ring_nf <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (ε / 2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (ε / 2 : ℝ) by linarith)]
    rw [h4, h5]
    constructor
    · -- Show that $-\epsilon < \epsilon/2 + (\epsilon/2)/4$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (ε / 2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (ε / 2 : ℝ) by linarith)]
    · -- Show that $\epsilon/2 + (\epsilon/2)/4 < \epsilon$
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (ε / 2 : ℝ) by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (ε / 2 : ℝ) by linarith)]