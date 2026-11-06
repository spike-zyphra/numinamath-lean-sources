import Mathlib

/- 4・150 Solve the system of equations

$$

\left\{\begin{array}{l}
\left|a_{1}-a_{2}\right| x_{2}+\left|a_{1}-a_{3}\right| x_{3}+\left|a_{1}-a_{4}\right| x_{4}=1, \\
\left|a_{2}-a_{1}\right| x_{1}+\left|a_{2}-a_{3}\right| x_{3}+\left|a_{2}-a_{4}\right| x_{4}=1, \\
\left|a_{3}-a_{1}\right| x_{1}+\left|a_{3}-a_{2}\right| x_{2}+\left|a_{3}-a_{4}\right| x_{4}=1, \\
\left|a_{4}-a_{1}\right| x_{1}+\left|a_{4}-a_{2}\right| x_{2}+\left|a_{4}-a_{3}\right| x_{3}=1 .
\end{array}\right.

$$


where $a_{1}, a_{2}, a_{3}, a_{4}$ are known distinct real numbers. -/
theorem algebra_272515 (a x : Fin 4 → ℝ) (ha : a.Injective)
    (h : ∀ i, ∑ j : Fin 4, abs (a i - a j) * x j = 1) :
    x = ![  1 / ((a ∘ Tuple.sort a) 3 - (a ∘ Tuple.sort a) 0),
            0,
            0,
            1 / ((a ∘ Tuple.sort a) 3 - (a ∘ Tuple.sort a) 0)] ∘ (Tuple.sort a).symm
  := by

    -- wlog, a is monotone
    wlog hw : Monotone a
    -- sorted injective function is injective
    · have c_inj : (a ∘ (Tuple.sort a)).Injective
        := ((Tuple.sort a).injective_comp a).mpr ha

      -- apply the theorem to the case when we have sorted a and x according to the values of a
      have sorted := this (a ∘ (Tuple.sort a)) (x ∘ (Tuple.sort a)) c_inj ?_ (Tuple.monotone_sort a)
      · -- sorting already sorted values does nothing
        have eq_id : Tuple.sort (a ∘ (Tuple.sort a)) = Equiv.refl (Fin 4)
          := Tuple.sort_eq_refl_iff_monotone.mpr <| Tuple.monotone_sort a

        -- so we can simplify
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, eq_id, Equiv.refl_apply,
          Equiv.refl_symm, Equiv.coe_refl, CompTriple.comp_eq] at sorted

        -- reorder functions
        exact (Equiv.eq_comp_symm (Tuple.sort a) x _).mpr sorted

      -- the equations are equal when permuting the variables
      -- we'll prove it by induction on permutation swaps
      · induction' (Tuple.sort a) using Equiv.Perm.swap_induction_on' with aa bb cc dd ee
        -- it's true for the identity permutation
        · simp only [Equiv.Perm.coe_one, Function.comp_apply, id_eq]
          assumption
        -- if it's true for some permuation, it's still true when you swap two elements.
        -- then we'll have that it's true for every permutation
        · intro ii
          have swapped_sum := ee ((Equiv.swap bb cc) ii)
          rw [←Equiv.sum_comp (Equiv.swap bb cc)] at swapped_sum
          exact swapped_sum

    -- so a is strictly monotone
    have a_strictmono : StrictMono a := hw.strictMono_of_injective ha

    -- then sorting of a is the identity
    rw [Tuple.sort_eq_refl_iff_monotone.mpr hw]

    -- simplify
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Equiv.coe_refl, Function.comp_apply,
      id_eq, one_div, Equiv.refl_symm, CompTriple.comp_eq]

    -- Given order of p and q, we can simplify |a p - a q|
    have abs_gen : ∀ {p q}, p < q → |a p - a q| = a q - a p := by
      intro p q h
      have neg : a p - a q < 0 := by
        simp only [sub_neg]
        exact a_strictmono h
      rw [abs_of_neg neg, neg_sub]

    have abs_gen' : ∀ {p q}, p < q → |a q - a p| = a q - a p := by
      intro p q h
      have pos : 0 < a q - a p := by
        simp only [sub_pos]
        exact a_strictmono h
      rw [abs_of_pos pos]

    -- specific cases of |a p - a q|
    have abs_0_1 : |a 0 - a 1| = a 1 - a 0 := abs_gen (by decide)
    have abs_0_2 : |a 0 - a 2| = a 2 - a 0 := abs_gen (by decide)
    have abs_0_3 : |a 0 - a 3| = a 3 - a 0 := abs_gen (by decide)
    have abs_1_2 : |a 1 - a 2| = a 2 - a 1 := abs_gen (by decide)
    have abs_1_3 : |a 1 - a 3| = a 3 - a 1 := abs_gen (by decide)
    have abs_2_3 : |a 2 - a 3| = a 3 - a 2 := abs_gen (by decide)
    have abs_1_0 : |a 1 - a 0| = a 1 - a 0 := abs_gen' (by decide)
    have abs_2_0 : |a 2 - a 0| = a 2 - a 0 := abs_gen' (by decide)
    have abs_2_1 : |a 2 - a 1| = a 2 - a 1 := abs_gen' (by decide)
    have abs_3_0 : |a 3 - a 0| = a 3 - a 0 := abs_gen' (by decide)
    have abs_3_1 : |a 3 - a 1| = a 3 - a 1 := abs_gen' (by decide)
    have abs_3_2 : |a 3 - a 2| = a 3 - a 2 := abs_gen' (by decide)

    -- we have four equations
    have sum_0 := h 0
    have sum_1 := h 1
    have sum_2 := h 2
    have sum_3 := h 3

    -- we simplify them, remove absolute values
    simp only [Fin.sum_univ_four, sub_self, abs_zero, zero_mul, zero_add, add_zero] at sum_0 sum_1 sum_2 sum_3
    simp only [abs_0_1, abs_0_2, abs_0_3] at sum_0
    simp only [abs_1_0, abs_1_2, abs_1_3] at sum_1
    simp only [abs_2_0, abs_2_1, abs_2_3] at sum_2
    simp only [abs_3_0, abs_3_1, abs_3_2] at sum_3

    -- we can subtract two equalities from each other
    have sub_of_eq : ∀ {p q r s : ℝ}, p = q → r = s → p - r = q - s := by
      intro p q r s h1 h2
      linarith

    -- subtract [2] from [1], [3] from [2] and [4] from [3]
    have sum_0_1 := sub_of_eq sum_0 sum_1
    have sum_1_2 := sub_of_eq sum_1 sum_2
    have sum_2_3 := sub_of_eq sum_2 sum_3

    -- seperate a and x into seperate factors in equalities
    convert_to (a 0 - a 1) * (x 1 + x 2 + x 3 - x 0) = 0 at sum_0_1
    · linarith
    · linarith only
    convert_to (a 1 - a 2) * (-x 0 - x 1 + x 2 + x 3) = 0 at sum_1_2
    · linarith
    · linarith only
    convert_to (a 2 - a 3) * (-x 0 - x 1 - x 2 + x 3) = 0 at sum_2_3
    · linarith
    · linarith only

    -- LHS a-factors are not zero
    have ne_0_1 : (a 0 - a 1) ≠ 0 := by
      have lt : a 0 < a 1 := a_strictmono (Fin.coe_sub_iff_lt.mp rfl)
      linarith only [lt]
    have ne_1_2 : (a 1 - a 2) ≠ 0 := by
      have lt : a 1 < a 2 := a_strictmono (Fin.coe_sub_iff_lt.mp rfl)
      linarith only [lt]
    have ne_2_3 : (a 2 - a 3) ≠ 0 := by
      have lt : a 2 < a 3 := a_strictmono (Fin.coe_sub_iff_lt.mp rfl)
      linarith only [lt]

    -- so other LHS factor must be zero
    simp only [ne_0_1, mul_eq_zero, false_or] at sum_0_1
    simp only [ne_1_2, mul_eq_zero, false_or] at sum_1_2
    simp only [ne_2_3, mul_eq_zero, false_or] at sum_2_3

    -- then we see that x 1 = x 2 = 0
    have x_1 : x 1 = 0 := by linarith only [sum_0_1, sum_1_2]
    have x_2 : x 2 = 0 := by linarith only [sum_1_2, sum_2_3]

    -- simplifying first equation gives (a 3 - a 0) * x 3 = 1
    simp only [x_1, mul_zero, x_2, add_zero, zero_add] at sum_0

    -- simplifying fourth equation gives (a 3 - a 0) * x 0 = 1
    simp only [x_1, mul_zero, add_zero, x_2] at sum_3

    -- now we know x 0, x 1, x 2, x 3
    ext i
    fin_cases i
    -- divide both sides by (a 3 - a 0)
    · exact (DivisionMonoid.inv_eq_of_mul (a 3 - a 0) (x 0) sum_3).symm
    · exact x_1
    · exact x_2
    -- divide both sides by (a 3 - a 0)
    · exact (DivisionMonoid.inv_eq_of_mul (a 3 - a 0) (x 3) sum_0).symm