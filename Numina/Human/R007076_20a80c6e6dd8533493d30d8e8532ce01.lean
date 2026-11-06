import Mathlib

open Polynomial

/- Given that three roots of $f(x)=x^4+ax^2+bx+c$ are $2$, $-3$, and $5$, what is the value of $a+b+c$? -/
theorem algebra_18728 (a b c : ℝ) (f : ℝ → ℝ)
    (h₀ : f = fun x => x ^ 4 + a * x ^ 2 + b * x + c)
    (h₁ : f 2 = 0) (h₂ : f (-3) = 0) (h₃ : f 5 = 0) :
    a + b + c = 79 := by
  -- We first prove that $f$ is a polynomial
  have h1 : f = (fun x => eval x (X ^ 4 + C a * X ^ 2 + C b * X + C c)) := by
    simp only [h₀]
    ext x
    simp only [coe_aeval_eq_eval, eval_add, eval_pow, eval_X, eval_mul, eval_C]
  -- We then prove that $f$ has the roots $2, -3, 5, 4$
  have h2 : X ^ 4 + C a * X ^ 2 + C b * X + C c = (X - 2) * (X + 3) * (X - 5) * (X + 4) := by
    -- $f$ has the roots $2, -3, 5$, so it is divisible by $(X - 2)(X + 3)(X - 5)$
    have root1 : IsRoot (X ^ 4 + C a * X ^ 2 + C b * X + C c) 2 := by
      simp only [IsRoot, eval_sub, eval_X, eval_C]
      have mid : f 2 = eval 2 (X ^ 4 + C a * X ^ 2 + C b * X + C c) := by
        rw [h1]
      rw [← mid, h₁]
    apply dvd_iff_isRoot.mpr at root1
    have root2 : IsRoot (X ^ 4 + C a * X ^ 2 + C b * X + C c) (-3) := by
      simp only [IsRoot, eval_sub, eval_X, eval_C]
      have mid : f (-3) = eval (-3) (X ^ 4 + C a * X ^ 2 + C b * X + C c) := by
        rw [h1]
      rw [← mid, h₂]
    apply dvd_iff_isRoot.mpr at root2
    have root3 : IsRoot (X ^ 4 + C a * X ^ 2 + C b * X + C c) 5 := by
      simp only [IsRoot, eval_sub, eval_X, eval_C]
      have mid : f 5 = eval 5 (X ^ 4 + C a * X ^ 2 + C b * X + C c) := by
        rw [h1]
      rw [← mid, h₃]
    apply dvd_iff_isRoot.mpr at root3
    have dvd : (X - C 2) * (X + C 3) * (X - C 5) ∣ (X ^ 4 + C a * X ^ 2 + C b * X + C c) := by
      refine IsCoprime.mul_dvd ?_ ?_ root3
      -- We prove that $(X - 2)(X + 3)$ and $(X - 5)$ are coprime
      refine IsCoprime.mul_left_iff.mpr ?_
      constructor
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      simp only [Nat.cast_ofNat, isUnit_iff_ne_zero]
      norm_num
      rw [← sub_neg_eq_add]
      show IsCoprime (X - (- C 3)) (X - C 5)
      rw [← C_neg]
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      simp only [Nat.cast_ofNat, isUnit_iff_ne_zero]
      norm_num
      rw [← sub_neg_eq_add]
      -- We prove that $(X - 2) * (X + 3) \dvd (X - 5)$
      show (X - 2) * (X - - C 3) ∣ X ^ 4 + C a * X ^ 2 + C b * X + C c
      rw [← C_neg]
      refine IsCoprime.mul_dvd ?_ ?_ root2
      apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
      simp only [Nat.cast_ofNat, isUnit_iff_ne_zero]
      norm_num
      exact root1
    rcases dvd with ⟨g, hg⟩
    -- We prove that $g = X + 4$ by proving that $g$ is a monic polynomial of degree $1$
    have geq : g.natDegree = 1 := by
      -- We prove that $X ^ 4 + C a * X ^ 2 + C b * X + C c$ is a polynomial of degree $4$
      have degeq : (X ^ 4 + C a * X ^ 2 + C b * X + C c).natDegree = 4 := by
        simp only [add_assoc]
        rw [natDegree_add_eq_left_of_degree_lt]
        exact natDegree_X_pow 4
        rw [← add_assoc]
        have mid : (C a * X ^ 2 + C b * X + C c).degree ≤ 2 := by exact degree_quadratic_le
        rw [degree_X_pow 4]
        show (C a * X ^ 2 + C b * X + C c : ℝ[X]).degree < 4
        have mid2 : (2 : WithBot ℕ) < 4 := by
          exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
        exact lt_of_le_of_lt mid mid2
      apply congrArg (fun x ↦ x.natDegree) at hg
      -- $X - 2 \neq 0$
      have neq1 : (X - 2 : ℝ[X]) ≠ 0 := by
        show (X - C 2) ≠ 0
        refine leadingCoeff_ne_zero.mp ?_
        rw [leadingCoeff_X_sub_C]
        exact Ne.symm (zero_ne_one' ℝ)
      -- $X + 3 \neq 0$
      have neq2 : (X + 3 : ℝ[X]) ≠ 0 := by
        show (X + C 3) ≠ 0
        refine leadingCoeff_ne_zero.mp ?_
        rw [leadingCoeff_X_add_C]
        exact Ne.symm (zero_ne_one' ℝ)
      -- $X - 5 \neq 0$
      have neq3 : (X - 5 : ℝ[X]) ≠ 0 := by
        show (X - C 5) ≠ 0
        refine leadingCoeff_ne_zero.mp ?_
        rw [leadingCoeff_X_sub_C]
        exact Ne.symm (zero_ne_one' ℝ)
      -- $g \neq 0$
      have neqg : g ≠ 0 := by
        intro h
        simp only [degeq, h, mul_zero, natDegree_zero, OfNat.ofNat_ne_zero] at hg
      rw [natDegree_mul, natDegree_mul, natDegree_mul, degeq] at hg
      simp only [natDegree_sub_C, natDegree_X, natDegree_add_C, Nat.reduceAdd] at hg
      exact Eq.symm (Nat.add_left_cancel hg)
      exact neq1
      exact neq2
      exact mul_ne_zero neq1 neq2
      exact neq3
      refine mul_ne_zero ?_ neq3
      exact mul_ne_zero neq1 neq2
      exact neqg
    -- We prove that $g$ is monic
    have monicg : Monic g := by
      have : Monic ((X - C 2 : ℝ[X]) * (X + C 3) * (X - C 5)) := by
        refine Monic.mul ?_ ?_
        refine Monic.mul ?_ ?_
        exact monic_X_sub_C 2
        exact monic_X_add_C 3
        exact monic_X_sub_C 5
      refine Monic.of_mul_monic_left this ?hpq
      rw [← hg]
      simp only [add_assoc]
      refine Monic.add_of_left ?_ ?_
      exact monic_X_pow 4
      have mid : (C a * X ^ 2 + C b * X + C c).degree ≤ 2 := by exact degree_quadratic_le
      rw [degree_X_pow 4, ← add_assoc]
      show (C a * X ^ 2 + C b * X + C c : ℝ[X]).degree < 4
      have mid2 : (2 : WithBot ℕ) < 4 := by
        exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
      exact lt_of_le_of_lt mid mid2
    -- We prove that $g$ is linear
    apply Monic.eq_X_add_C monicg at geq
    show X ^ 4 + C a * X ^ 2 + C b * X + C c = (X - C 2) * (X + C 3) * (X - C 5) * (X + C 4)
    -- We prove that $g = X + 4$
    have gcoe : g.coeff 0 = 4 := by
      rw [geq] at hg
      apply congrArg (fun x ↦ x.coeff 3) at hg
      ring_nf at hg
      simp only [X_mul_C, X_pow_mul_C, coeff_add, coeff_C_mul, coeff_X, OfNat.one_ne_ofNat, ↓reduceIte, mul_zero, coeff_X_pow, OfNat.ofNat_eq_ofNat, Nat.succ_ne_self, add_zero, Nat.reduceEqDiff, coeff_C, OfNat.ofNat_ne_zero, mul_assoc, coeff_sub, sub_self, coeff_neg, neg_zero, mul_one, zero_sub, zero_add, coeff_mul_C, zero_mul] at hg
      symm at hg
      rw [add_comm] at hg
      apply eq_sub_of_add_eq at hg
      norm_num at hg
      exact hg
    rw [hg, geq, gcoe]
  -- We prove that $a + b + c = 79$ by considering the value of $f(1)$
  apply congrArg (fun x => aeval (1: ℝ) x) at h2
  simp only [coe_aeval_eq_eval, eval_add, eval_pow, eval_X, one_pow, eval_mul, eval_C, mul_one, eval_sub, eval_ofNat] at h2 
  rw [add_assoc 1, add_assoc 1, add_comm 1] at h2
  apply eq_sub_of_add_eq at h2
  norm_num at h2
  exact h2



