import Mathlib

/- $4 \cdot 134$ Given the system of equations

$$

\left\{\begin{array}{l}
a_{11} x_{1}+a_{12} x_{2}+a_{13} x_{3}=0, \\
a_{21} x_{1}+a_{22} x_{2}+a_{23} x_{3}=0, \\
a_{31} x_{1}+a_{32} x_{2}+a_{33} x_{3}=0 .
\end{array}\right.

$$


The coefficients satisfy the following conditions:
(1) $a_{11}, a_{22}$, and $a_{33}$ are positive;
(2) All other coefficients are negative;
(3) The sum of the coefficients in each equation is positive.

Prove: $x_{1}=x_{2}=x_{3}=0$ is the only solution to the given system of equations. -/
theorem algebra_160103 (x : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ)
    (hpos : a 0 0 > 0 ∧ a 1 1 > 0 ∧ a 2 2 > 0)
    (hneg : ∀ i j, i ≠ j → a i j < 0)
    (hsum : ∀ i, a i 0 + a i 1 + a i 2 > 0)
    (heq : ∀ i, a i 0 * x 0 + a i 1 * x 1 + a i 2 * x 2 = 0) :
    ∀ i, x i = 0 := by

    -- use < instead of >
    simp only [gt_iff_lt] at hpos hsum


    -- wlog, we have |x_0| ≤ |x_1| ≤ |x_2|
    wlog hm : Monotone (abs ∘ x)
    · let g := Tuple.sort (abs ∘ x)
      have neg : ∀ i j, i ≠ j → a (g i) (g j) < 0 := by
        intro i j ij
        apply hneg
        exact fun a => ij (g.injective a)

        -- write row sum using ∑
      have sum_eq_zero : ∀ (i : Fin 3), ∑ j : Fin 3, a i j * x j = 0 := by
        intro i
        rw [Fin.sum_univ_three]
        exact heq i

      -- if we have proven the theorem when |x_k| is monotone, then we can prove the theorem for every case by sorting x and a indicies according to the order of |x_k|
      intro i
      have applied := this (x ∘ g) (fun i j => a (g i) (g j)) neg ?_ ?_ ?_ (Tuple.monotone_sort (abs ∘ x)) (g.symm i)
      simp only [Function.comp_apply, Equiv.apply_symm_apply] at applied
      exact applied
      -- rows are equal to zero
      · simp only [Function.comp_apply]
        intro i
        -- sums are invariant under index permutations
        have sum_app := sum_eq_zero (g i)
        rw [←Equiv.sum_comp g, Fin.sum_univ_three] at sum_app
        exact sum_app
      -- variables on diagonal are still positive after permutation
      · have pos_alt : ∀ i, 0 < a i i := by
          intro i
          fin_cases i
          · exact hpos.1
          · exact hpos.2.1
          · exact hpos.2.2

        exact ⟨pos_alt (g 0), pos_alt (g 1), pos_alt (g 2)⟩
      -- sum of coefficients are still positive
      · intro i
        -- write sum using ∑
        have hsum_alt : ∀ i, 0 < ∑ j, a i j := by
          intro i
          rw [Fin.sum_univ_three]
          exact hsum i

        have hsum_app := hsum_alt (g i)
        rw [←Equiv.sum_comp g, Fin.sum_univ_three] at hsum_app
        exact hsum_app

    -- inequality on last row
    have le_abs_row : |a 2 2 * x 2| - |a 2 1 * x 1| - |a 2 0 * x 0|
      ≤ |a 2 2 * x 2 + a 2 1 * x 1 + a 2 0 * x 0| := by
      -- chain (in-)equalities, mostly |a| - |b| ≤ |a - b|
      calc |a 2 2 * x 2| - |a 2 1 * x 1| - |a 2 0 * x 0|
      _ = |a 2 2 * x 2| - |-(a 2 1 * x 1)| - |-(a 2 0 * x 0)| := by simp only [abs_neg]
      _ ≤ |a 2 2 * x 2 - -(a 2 1 * x 1)| - |-(a 2 0 * x 0)| := by
        gcongr
        exact abs_sub_abs_le_abs_sub _ _
      _ ≤ |a 2 2 * x 2 - -(a 2 1 * x 1) - -(a 2 0 * x 0)| := abs_sub_abs_le_abs_sub _ _
      _ = |a 2 2 * x 2 - -(a 2 1 * x 1) + (a 2 0 * x 0)| := by ring_nf
      _ = |a 2 2 * x 2 + a 2 1 * x 1 + a 2 0 * x 0| := by rw [sub_neg_eq_add]

    -- we know the signs of the coefficients, so we can extract them from the absolute values
    have terms_eq : a 2 2 * |x 2| + a 2 1 * |x 1| + a 2 0 * |x 0| = |a 2 2 * x 2| - |a 2 1 * x 1| - |a 2 0 * x 0| := by
      simp only [abs_mul, sub_eq_add_neg]
      congr 3
      · exact (abs_of_pos hpos.2.2).symm
      · suffices h : a 2 1 = -|a 2 1|
        · rw [h]
          simp only [neg_mul, abs_neg, abs_abs]
        have neg := hneg 2 1 (by omega)
        rw [abs_of_neg neg]
        exact (neg_neg (a 2 1)).symm
      · suffices h : a 2 0 = -|a 2 0|
        · rw [h]
          simp only [neg_mul, abs_neg, abs_abs]
        have neg := hneg 2 0 (by omega)
        rw [abs_of_neg neg]
        exact (neg_neg (a 2 0)).symm

    -- we know that |x_k| is monotone, so we have bounds on each term
    have terms_le : a 2 2 * |x 2| + a 2 1 * |x 2| + a 2 0 * |x 2| ≤ a 2 2 * |x 2| + a 2 1 * |x 1| + a 2 0 * |x 0| := by
      -- a_21 is negative, so a_21 * |x_2| ≤ a_21 * |x_1|
      have term_1 : a 2 1 * |x 2| ≤ a 2 1 * |x 1| := by
        refine (mul_le_mul_left_of_neg ?_).mpr ?_
        exact hneg 2 1 (by omega)
        apply hm
        omega
      -- a_20 is negative, so a_20 * |x_2| ≤ a_20 * |x_0|
      have term_2 : a 2 0 * |x 2| ≤ a 2 0 * |x 0| := by
        refine (mul_le_mul_left_of_neg ?_).mpr ?_
        exact hneg 2 0 (by omega)
        apply hm
        omega

      linarith only [term_1, term_2]

    -- we can factor out |x_2|
    have factor : a 2 2 * |x 2| + a 2 1 * |x 2| + a 2 0 * |x 2| = (a 2 2 + a 2 1 + a 2 0) * |x 2| := by ring

    -- after factoring, it's clear that it's non-negative
    have factor_nonneg : 0 ≤ (a 2 2 + a 2 1 + a 2 0) * |x 2| := by
      -- because the sum is non-negative
      have sum_nonneg : 0 ≤ (a 2 2 + a 2 1 + a 2 0) := by linarith only [hsum 2]
      positivity

    -- but we also have that it's non-positive
    have factor_nonpos : (a 2 2 + a 2 1 + a 2 0) * |x 2| ≤ 0 := by
      -- we chain the many inequalities we found
      calc (a 2 2 + a 2 1 + a 2 0) * |x 2|
      _ = a 2 2 * |x 2| + a 2 1 * |x 2| + a 2 0 * |x 2| := factor.symm
      _ ≤ a 2 2 * |x 2| + a 2 1 * |x 1| + a 2 0 * |x 0| := terms_le
      _ = |a 2 2 * x 2| - |a 2 1 * x 1| - |a 2 0 * x 0| := terms_eq
      _ ≤ |a 2 2 * x 2 + a 2 1 * x 1 + a 2 0 * x 0| := le_abs_row
      -- the row is equal to zero
      _ = |0| := by
        congr
        linarith only [heq 2]
      _ = 0 := abs_zero

    -- so (a_22 + a_21 + a_20) * |x 2| = 0
    have factor_eq_zero : (a 2 2 + a 2 1 + a 2 0) * |x 2| = 0
      := le_antisymm factor_nonpos factor_nonneg

    -- |x_2| = 0
    have x_two_eq : |x 2| = 0 := by
      -- a * b = 0 means a = 0 or b = 0
      cases' mul_eq_zero.mp factor_eq_zero with h1 h2
      -- but (a_22 + a_21 + a_20) is positive
      · linarith only [h1, hsum 2]
      -- so |x_2| = 0
      · exact h2

    -- |x_k| is monotone, so |x_1| = 0
    have x_one_eq : |x 1| = 0 := by
      have abs_le : |x 1| ≤ |x 2| := by
        apply hm
        omega

      have abs_pos : 0 ≤ |x 1| := abs_nonneg (x 1)
      linarith only [abs_le, abs_pos, x_two_eq]

    -- |x_k| is monotone, so |x_0| = 0
    have x_zero_eq : |x 0| = 0 := by
      have abs_le : |x 0| ≤ |x 2| := by
        apply hm
        omega

      have abs_pos : 0 ≤ |x 0| := abs_nonneg (x 0)
      linarith only [abs_le, abs_pos, x_two_eq]

    -- |x| = 0 implies x = 0, so we have x_0 = 0, x_1 = 0, x_2 = 0
    rw [abs_eq_zero] at x_zero_eq x_one_eq x_two_eq

    -- we found the values of all x_k
    intro i
    fin_cases i
    · exact x_zero_eq
    · exact x_one_eq
    · exact x_two_eq