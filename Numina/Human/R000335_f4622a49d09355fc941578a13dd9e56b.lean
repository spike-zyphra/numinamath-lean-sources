import Mathlib

/-
Find the number of permutations  $x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8$  of the integers  $-3, -2, -1, 0,1,2,3,4$  that satisfy the chain of inequalities   $$ x_1x_2\le x_2x_3\le x_3x_4\le x_4x_5\le x_5x_6\le x_6x_7\le x_7x_8. $$  
-/
theorem number_theory_8967
    (s : List ℤ) (satisfiesCondition : List ℤ → Bool)
    (hs : s = [-3, -2, -1, 0, 1, 2, 3, 4])
    (hsat : satisfiesCondition = fun x =>
      match x with
      | [x1, x2, x3, x4, x5, x6, x7, x8] =>
        x1 * x2 ≤ x2 * x3 ∧ x2 * x3 ≤ x3 * x4 ∧ x3 * x4 ≤ x4 * x5 ∧ x4 * x5 ≤ x5 * x6 ∧ x5 * x6 ≤ x6 * x7 ∧ x6 * x7 ≤ x7 * x8
      | _ => false ) :
    (s.permutations.filter satisfiesCondition).length = 21 := by
  rw [hs, hsat]
  native_decide
