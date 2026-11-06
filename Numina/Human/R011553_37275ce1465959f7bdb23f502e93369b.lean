import Mathlib

open Real Set
open scoped BigOperators

/- 7. [6 points] Find all values of the parameter $a$, for each of which the system

$$

\left\{\begin{array}{l}
|y+x+8|+|y-x+8|=16 \\
(|x|-15)^{2}+(|y|-8)^{2}=a
\end{array}\right.

$$

has exactly two solutions. -/

theorem algebra_150937 (a : ℝ) :
    {(x, y): ℝ × ℝ | abs (y + x + 8) + abs (y - x + 8) = 16 ∧ (abs x - 15)^2 + (abs y - 8)^2 = a}.encard = 2 ↔
    a = 49 ∨ a = 289 := by

  -- absolute value of real number as expression with condition
  have abs_with_ifs (t: ℝ): abs t = if t < 0 then - t else t := by
    split <;> rename_i H
    . rw [abs_of_neg H]
    . rw [abs_of_nonneg (le_of_not_lt H)]

  -- first equation of the system as expression with conditions
  have first_equation_with_ifs (x y: ℝ):
      abs (y + x + 8) + abs (y - x + 8) = 16 ↔
      if y + x + 8 < 0
      then if y - x + 8 < 0
           then y = -16
           else x = -8
      else if y - x + 8 < 0
           then x = 8
           else y = 0 := by
    simp only [abs_with_ifs]
    split_ifs <;> constructor <;> intro H0 <;> linarith

  -- this result will be used to prove that cardinality of a set isn't 2,
  -- if it has three different elements `x`, `y`, `z`
  have encard_ne_two_if_three_different_elements {A: Type} (S: Set A) (x y z: A) (Hx: x ∈ S) (Hy: y ∈ S)
      (Hz: z ∈ S) (Hxy: x ≠ y) (Hxz: x ≠ z) (Hyz: y ≠ z):
      S.encard ≠ 2 := by
    intros H0
    -- set has cardinality equal to 2 iff it has exactly two different elements (`a` and `b`)
    rw [encard_eq_two] at H0
    -- let's obtain `a` and `b` annd use these variables in the proof
    obtain ⟨a, b, H0, H1⟩ := H0
    -- two sets are equal iff every value is either in both sets or in none
    rw [Set.ext_iff] at H1
    -- all three elements of the set `S` is also elements of the set `{a, b}`
    rw [H1] at Hx Hy Hz
    -- if element is element of the set `{a, b}` then it is either equal to `a` or equal to `b`
    simp only [mem_insert_iff, mem_singleton_iff] at Hx Hy Hz
    -- there are two possibilities for `x` (`x` equal to `a` or `x` equal to `b`),
    -- for `y` (`y` equal to `a` or `y` equal to `b`) and
    -- for `z` (`z` equal to `a` or `z` equal to `b`)
    -- that means in total 8 possibilities, each leading to contradiction
    obtain Hx | Hx := Hx <;> obtain Hy | Hy := Hy <;> obtain Hz | Hz := Hz <;>
    subst x y z <;> tauto

  -- let's use abbreviation `S` for the set of solutions of the given system
  set S := {(x, y): ℝ × ℝ | abs (y + x + 8) + abs (y - x + 8) = 16 ∧ (abs x - 15)^2 + (abs y - 8)^2 = a}

  -- there are six relevant cases for the value of parameter `a`
  -- 1) a < 49, the system has no solutions
  -- 2) a = 49, the system has two solutions
  -- 3) 49 < a ∧ a ≤ 113, the system has at least three solutions
  -- 4) 113 < a ∧ a < 289, the system has at least three solutions
  -- 5) a = 289, the system has two solutions
  -- 6) 289 < a, the system has no solutions

  have all_relevant_cases: a < 49 ∨ a = 49 ∨ 49 < a ∧ a ≤ 113 ∨ 113 < a ∧ a < 289 ∨ a = 289 ∨ 289 < a := by
    obtain H | H | H := lt_trichotomy a 49
    . tauto
    . tauto
    . obtain H0 | H0 := le_or_lt a 113
      . tauto
      . obtain H1 | H1 | H1 := lt_trichotomy a 289
        . tauto
        . tauto
        . tauto

  obtain case1 | case2 | case3 | case4 | case5 | case6 := all_relevant_cases

  . -- let's prove - if a < 49 then the set of solutions is empty
    have S_is_empty: S = ∅ := by
      -- let's unfold the abbreviature `S`
      simp only [S]
      -- the solution set is empty iff it has no members
      -- we need to prove that in this specific case
      -- there's no solution to the given system;
      -- that will be done by introducing such solution and reaching contradiction
      simp only [eq_empty_iff_forall_not_mem, mem_setOf_eq, not_and, Prod.forall]
      intros x y H1 H2
      -- let's replace absolute values in the first equation
      -- with expression that contains conditionals
      -- and then look at the each case in it
      rw [first_equation_with_ifs] at H1
      split_ifs at H1 <;> rename_i H3 H4
      . subst y
        norm_num at H2
        -- sum of square and 64 will always be more than 49, but a is less than 49
        nlinarith
      . subst x
        norm_num at H2
        -- sum of 49 and square is at least 49, but a is less than 49
        nlinarith
      . subst x
        norm_num at H2
        -- sum of 49 and square is at least 49, but a is less than 49
        nlinarith
      . subst y
        norm_num at H2
        -- sum of 49 and suqare is at least 49, but a is less than 49
        nlinarith

    -- let's use the fact that we just proved - that the set of solutions is empty and simplify the goal
    simp only [S_is_empty, encard_empty, OfNat.zero_ne_ofNat, false_iff, not_or]
    -- the goal now can be proven by linarith tactic after some preprocessing
    constructor <;> intro H <;> linarith

  . -- if the parameter `a` is equal to 49, then there are exactly two solutions of the system
    have S_has_two_solutions: S = {(-8, -8), (8, -8)} := by
      -- unfold the abbreviature `S` and substitute parameter with the value 49
      simp only [S]
      subst a
      -- use set extensionality and simplify
      ext ⟨x, y⟩
      simp only [mem_setOf_eq, mem_insert_iff, Prod.mk.injEq, mem_singleton_iff]
      -- now the goal is double implication
      constructor <;> intro H2
      . -- direction from left to right
        -- destruct the conjuction `H2`
        obtain ⟨H2, H3⟩ := H2
        -- replace all absolute values in the equation `H2` with conditionals
        rw [first_equation_with_ifs] at H2
        -- look at each possible cases
        split_ifs at H2 <;> rename_i H4 H5
        . -- substitute value of variable `y` everywhere and simplify everything using `norm_num`
          subst y
          norm_num at *
          -- there is no way for sum of square and 65 to be equal to 49
          nlinarith
        . -- substitute value of variable `x` everywhere and simplify everything using `norm_num`
          subst x
          norm_num at *
          -- now we know that `y` is negative, so absolute value of `y` is equal to `- y`
          rw [abs_of_neg H4] at H3
          -- `linarith` proves the goal
          linarith
        . -- substitute value of variable `x` everywhere and simplify everything using `norm_num`
          subst x
          norm_num at *
          -- now we know that `y` is negative, so absolute value of `y` is equal to `- y`
          rw [abs_of_neg H5] at H3
          -- `linarith` proves the goal
          linarith
        . -- substitue value of variable `y` everywhere and simplify everything using `norm_num`
          subst y
          norm_num at *
          -- there is no way for sum of square and 64 to be equal to 49
          nlinarith
      . -- direction from right to left
        -- destruct the hypothesis H2 as much as possible
        obtain ⟨Hx, Hy⟩ | ⟨Hx, Hy⟩ := H2
        . -- substitute x and y everywhere and then simplify
          subst x y
          norm_num
        . -- substitute x and y everywhere and then simplify
          subst x y
          norm_num

    -- let's use the lemma `S_has_two_solutions` and replace `S` with its value in the goal
    -- also use the fact that parameter `a` is equal to `49` to simplify
    simp only [S_has_two_solutions, case2, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, or_false,
      iff_true]
    -- now we only have to prove that given set has cardinality equal to 2
    rw [encard_eq_two]
    use (-8, -8), (8, -8)
    simp only [ne_eq, Prod.mk.injEq, and_true]
    norm_num

  . -- the right side of the double implication can be simplified,
    -- because `a` isn't equal to 49 and also isn't equal to 289
    have H: a ≠ 49 := by linarith
    have H0: a ≠ 289 := by linarith
    simp only [H, H0, or_self, iff_false, ne_eq]

    -- let's prove two useful results (`H5` and `H6`)
    have H5: √(a - 49) ≤ 8 := by
      rw [sqrt_le_iff]
      constructor <;> linarith
    have H6: 0 < √(a - 49) := by
      rw [sqrt_pos]
      linarith

    -- let's use theorem `encard_ne_two_if_three_different_elements`
    -- with specific three values `x`, `y`, `z`
    apply encard_ne_two_if_three_different_elements S
      (-8, -8 - √(a - 49)) (-8, √(a - 49) - 8) (8, -8 - √(a - 49))
    . -- unfold the abbreviature `S` and simplify the goal
      simp only [S, mem_setOf_eq, neg_add_cancel_right, sub_neg_eq_add, abs_neg, Nat.abs_ofNat]
      constructor
      . ring_nf at H5 H6 ⊢
        -- get rid of absolute value functions in the goal and use tactic `ring`
        rw [abs_of_neg (by linarith)]
        rw [abs_of_nonneg (by linarith)]
        ring
      . -- get rid of absolute value function in the goal
        rw [abs_of_neg (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- that means the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- unfold the abbreviature `S` and simplify the goal
      simp only [S, mem_setOf_eq, neg_add_cancel_right, sub_neg_eq_add, sub_add_cancel, abs_neg,
      Nat.abs_ofNat]
      constructor
      . -- get rid of absolute value functions in the goal and use tactic `ring`
        rw [abs_of_nonpos (by linarith)]
        rw [abs_of_pos (by linarith)]
        ring
      . -- get rid of absolute value function in the goal
        rw [abs_of_nonpos (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- unfold the abbreviature `S` and simplify the goal
      simp only [S, mem_setOf_eq, sub_add_cancel, Nat.abs_ofNat]
      constructor
      . ring_nf at H5 H6 ⊢
        -- get rid of absolute value functions in the goal and use tactic `ring`
        rw [abs_of_nonneg (by linarith)]
        rw [abs_of_neg (by linarith)]
        ring
      . -- get rid of absolute value function in the goal
        rw [abs_of_neg (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- the first values for both pairs are equal, they can be simplified away
      simp only [ne_eq, Prod.mk.injEq, true_and]
      -- `linarith` solves the goal
      linarith
    . -- the first values for both pairs are different
      -- simple `norm_num` suffices
      norm_num
    . -- the first values for both pairs are different
      -- simple `norm_num` suffices
      norm_num

  . -- the right side of the double implication can be simplified,
    -- because `a` isn't equal to 49 and also isn't equal to 289
    have H: a ≠ 49 := by linarith
    have H0: a ≠ 289 := by linarith
    simp only [H, H0, or_self, iff_false, ne_eq]

    -- let's prove two useful results (`H5` and `H6`)
    have H5: √(a - 64) < 15 := by
      rw [sqrt_lt' (by linarith)]
      linarith
    have H6: 7 < √(a - 64) := by
      rw [lt_sqrt (by linarith)]
      linarith

    -- let's use theorem `encard_ne_two_if_three_different_elements`
    -- with specific three values `x`, `y`, `z`
    apply encard_ne_two_if_three_different_elements S
      (15 - √(a - 64), 0) (15 - √(a - 64), -16) (√(a - 64) - 15, 0)
    . -- unfold the abbreviature `S` and simplify
      simp only [S, mem_setOf_eq, zero_add, zero_sub, neg_sub, abs_zero, even_two, Even.neg_pow]
      constructor
      . -- get rid of absolute value functions in the goal and use tactic `ring`
        ring_nf at H5 H6 ⊢
        rw [abs_of_pos (by linarith)]
        rw [abs_of_pos (by linarith)]
        ring
      . -- get rid of absolute value function in the goal
        rw [abs_of_pos (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- that means the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- unfold the abbreviature `S` and simplify
      simp only [S, mem_setOf_eq, abs_neg, Nat.abs_ofNat]
      constructor
      . -- get rid of absolute value functions in the goal and use tactic `ring`
        ring_nf at H5 H6 ⊢
        rw [abs_of_neg (by linarith)]
        rw [abs_of_neg (by linarith)]
        ring
      . -- get rid of absolute value function in the goal and use tactic `ring`
        rw [abs_of_pos (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- that means the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- unfold the abbreviature `S` and simplify
      simp only [S, mem_setOf_eq, zero_add, zero_sub, neg_sub, abs_zero, even_two, Even.neg_pow]
      constructor
      . -- get rid of absolute value functions in the goal and use tactic `ring`
        ring_nf at H5 H6 ⊢
        rw [abs_of_pos (by linarith)]
        rw [abs_of_pos (by linarith)]
        ring
      . -- get rid of absolute value function in the gaol
        rw [abs_of_neg (by linarith)]
        -- simplify the goal using `ring_nf` tactic
        ring_nf
        -- expression under the square root sign is positive
        -- that means the squared square root can be simplified
        rw [sq_sqrt (by linarith)]
        -- now the `ring` tactic solves the goal
        ring
    . -- the second values for both pairs are different, simple `norm_num` suffices
      norm_num
    . -- the second values for both pairs are equal
      -- therefoe they can be simplified away
      simp only [ne_eq, Prod.mk.injEq, and_true]
      -- now `linarith` solves the goal
      linarith
    . -- the second values for both pairs are different, simple `norm_num` sufficrs
      norm_num

  . -- if the parameter `a` is equal to 289, then there are exactly two solutions of the system
    have S_has_two_solutions: S = {(0, 0), (0, -16)} := by
      -- unfold the abbreviature `S` and substitute parameter with the value 289
      simp [S]
      subst a
      -- use set extensionality and simplify
      ext ⟨x, y⟩
      simp only [mem_setOf_eq, mem_insert_iff, Prod.mk_eq_zero, mem_singleton_iff, Prod.mk.injEq]
      -- now the goal is double implication
      -- destruct it and prove both directions
      constructor <;> intro H6
      . -- direction from left to right
        -- destruct the conjunction `H6`
        obtain ⟨H6, H7⟩ := H6
        -- replace absolute value functions with conditionals in `H6`
        rw [first_equation_with_ifs] at H6
        -- look at each possible case
        split_ifs at H6 <;> rename_i H8 H9
        . -- substitute `y` everywhere and simplify everything with `norm_num`
          subst y
          norm_num at *
          -- calculate value of `(abs x - 15) ^ 2` and then take square root of it
          have H10: (abs x - 15) ^ 2 = 15 ^ 2 := by linarith
          rw [sq_eq_sq_iff_eq_or_eq_neg] at H10
          -- destruct the disjunction `H10`
          obtain H10 | H10 := H10
          . -- replace absolute value function in `H10` with conditional
            rw [abs_with_ifs] at H10
            -- split `H10` into different possible cases and use `linarith` in each case
            split_ifs at H10 <;> rename_i H11 <;> linarith
          . -- in this case one can prove that `abs x` is equal to 0, using `linarith`
            have H11: abs x = 0 := by linarith
            -- that is simplified to `x = 0`, which is exactly the goal
            simp only [abs_eq_zero] at H11
            exact H11
        . -- substitute `x` everywhere and simplify everything with `norm_num`
          subst x
          norm_num at *
          -- get rid of absolute value function in `H7`
          rw [abs_of_neg H8] at H7
          -- goal is solved using `nlinarith`
          nlinarith
        . -- substitute `x` everywhere and simplify everything with `norm_num`
          subst x
          norm_num at *
          -- get rid of absolute value function in `H7`
          rw [abs_of_neg H9] at H7
          -- goal is solved using `nlinarith`
          nlinarith
        . -- substitute `y` everywhere and simplify everything with `norm_num`
          subst y
          norm_num at *
          -- calculate value of `(abs x - 15) ^ 2` and then take square root of it
          have H10: (abs x - 15) ^ 2 = 15 ^ 2 := by linarith
          rw [sq_eq_sq_iff_eq_or_eq_neg] at H10
          -- destruct the disjunction `H10`
          obtain H10 | H10 := H10
          . -- get rid of absolute value function in `H10`
            rw [abs_with_ifs] at H10
            -- look at each of possible cases and prove the goal using `linarith`
            split_ifs at H10 <;> rename_i H11 <;> linarith
          . -- one can prove that `abs x` is equal to 0, using `linarith`
            have H11: abs x = 0 := by linarith
            -- that is simplified to `x = 0`, which is exactly the goal
            simp at H11
            exact H11
      . -- direction from right to left
        -- destruct the hypothesis H6 as much as possible
        obtain ⟨Hx, Hy⟩ | ⟨Hx, Hy⟩ := H6
        . -- substitute `x` and `y` and then simplify the goal using `norm_num`
          subst x y
          norm_num
        . -- substitute `x` and `y` and then simplify the goal using `norm_num`
          subst x y
          norm_num

    -- use the fact `S_has_two_solutions` to replace `S` with concrete set
    -- also substitute `a` and simplify the goal
    rw [S_has_two_solutions]
    subst a
    simp only [OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, or_true, iff_true]
    -- now prove that the concrete set has cardinality equal to 2
    rw [encard_eq_two]
    use (0, 0), (0, -16)
    -- simplify to solve the goal
    simp only [ne_eq, Prod.mk.injEq, zero_eq_neg, OfNat.ofNat_ne_zero, and_false, not_false_eq_true,
      and_self]

  . -- if 289 < a, then the set `S` is empty
    have S_is_empty: S = ∅ := by
      -- unfold the abbteviature S and use set extensionality, then simplify and `intro`
      simp only [S]
      ext ⟨x, y⟩
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intros H7 H8
      -- replace absolute value functions in `H7` with conditionals
      rw [first_equation_with_ifs] at H7
      -- split `H7` into all possible cases
      split_ifs at H7 <;> rename_i H9 H10
      . -- substitute `y` everywhere and simplify everything using `norm_num`
        subst y
        norm_num at *
        -- remove absolute value function from `H8`, using `abs_with_ifs`
        -- then split `H8` into all possible cases and solve goals using `nlinarith`
        rw [abs_with_ifs] at H8
        split_ifs at H8 <;> rename_i H11 <;> nlinarith
      . -- substitute `x` everywhere and simplify everything using `norm_num`
        subst x
        norm_num at *
        -- as y < 0 (hypothesis `H9`), one can get rid of absolute value function in H8
        rw [abs_of_neg H9] at H8
        -- goal is solved by `nlinarith`
        nlinarith
      . -- substitute `x` everywhere and simplify everything using `norm_num`
        subst x
        norm_num at *
        -- as y < 0 (hypothesis `H9`), one can get rid of absolute value function in H8
        rw [abs_of_neg H10] at H8
        -- goal is solved by `nlinarith`
        nlinarith
      . -- substitute `y` everywhere and simplify everything using `norm_num`
        subst y
        norm_num at *
        -- remove absolute value function from `H8`, using `abs_with_ifs`
        rw [abs_with_ifs] at H8
        split_ifs at H8 <;> rename_i H11 <;> nlinarith
    
    -- use the lemma `S_is_empty` and replace `S` with empty set, then simplify
    simp only [S_is_empty, encard_empty, OfNat.zero_ne_ofNat, false_iff, not_or]
    -- prove both subgoals of conjunction by `linarith`
    constructor <;> linarith