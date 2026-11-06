import Mathlib

open Real

/- 13. Prove: The equation $(x+1)^{\log _{3} 2}=x$ has a unique positive real solution. -/

theorem algebra_202551 :
    ∃! x : ℝ, 0 < x ∧ (x + 1) ^ (logb 3 2) = x := by

    use 2
    constructor
    · -- First we show that x = 2 satisfy the equation
      simp
      norm_num
    · -- now we shoat that 2 is the unique solution
      simp_all
      -- suppose otherwise, there is another solution x with x > 0 also satisfy the equation
      intro x xpos xeq
      -- Take log with base (x + 1) at both sides, we show that
      -- logb (x + 1) x = logb 3 2
      have : logb (x + 1) ((x + 1) ^ (logb 3 2)) = logb 3 2 := by
        refine logb_rpow ?b_pos ?b_ne_one
        <;> linarith
      have xeq₁: logb (x + 1) x = logb 3 2 := by
        rw [← this, xeq]

      -- define an auxiliary variable t such that x + 1 = 3 ^ t
      let t := logb 3 (x + 1)
      have teq : 3 ^ t = x + 1 := by
        unfold t;
        apply rpow_logb
        all_goals linarith

      -- we show that logb (3 ^ t) x = logb 3 2 by taking the definition of t.
      have teq₁ : logb (3 ^ t) x = logb 3 2 := by
        rw [teq]
        assumption

      -- changing the base from 3 ^ t to 3
      have : logb (3 ^ t) x = (logb 3 x) / (logb 3 (3 ^ t)) := by
        field_simp [logb]
      simp at this

      -- so the equation becomes logb 3 x / t = logb 3 2
      rw [this] at teq₁

      -- move the term t to the RHS.
      have teq₂ : logb 3 x = t * logb 3 2 := by
        rw [mul_comm]
        apply (div_eq_iff ?_).mp
        assumption
        unfold t
        apply logb_ne_zero_of_pos_of_ne_one
        all_goals linarith

      -- then, use basic identity of logb
      have : t * logb 3 2 = logb 3 (2 ^ t) := by
        symm
        apply logb_rpow_eq_mul_logb_of_pos
        linarith
      -- the equation changes to logb 3 x = logb 3 (2 ^ t)
      rw [this] at teq₂

      -- as logb is injective, we obtain x = 2 ^ t
      have xt_eq : x = 2 ^ t := by
        apply Real.logb_injOn_pos (show 3 > 1 by norm_num)
        simp_all
        simp
        refine rpow_pos_of_pos ?_ t
        linarith
        assumption

      -- by definition, x + 1 = 3 ^ t, combining with what we just obtain,
      -- we deduce 3 ^ t = 2 ^ t + 1
      rw [xt_eq] at teq

      -- dividing 3 ^ t from both sides:
      have teq₃ : (2 / (3 : ℝ)) ^ t + (1 / (3 : ℝ)) ^ t = 1 := by
        rw [div_rpow (by norm_num) (by norm_num), div_rpow (by norm_num) (by norm_num)]
        field_simp
        linarith

      -- finally we prove by contradiction that x = 2
      by_contra!
      -- if x ≠ 2, then we must have t ≠ 1
      have tne1 : t ≠ 1 := by by_contra! ht; rw [ht] at xt_eq; simp at xt_eq; contradiction

      -- but then the equation (2/3)^t + (1/3)^t = 1 cannot hold
      -- this is proved by a case analysis of whether t < 1 or t > 1
      rcases lt_or_gt_of_ne tne1 with tlt1 | tgt1
      · have h1 : (2 / (3 : ℝ)) ^ t > (2 / (3 : ℝ)) ^ (1 : ℝ) := by
          apply (Real.rpow_lt_rpow_left_iff_of_base_lt_one ?_ ?_).mpr
          assumption
          all_goals norm_num
        have h2 : (1 / (3 : ℝ)) ^ t > (1 / (3 : ℝ)) ^ (1 : ℝ) := by
          apply (Real.rpow_lt_rpow_left_iff_of_base_lt_one ?_ ?_).mpr
          assumption
          all_goals norm_num
        rw [show (2 / (3 : ℝ)) ^ (1 : ℝ) = 2 / 3 by norm_num] at h1
        rw [show (1 / (3 : ℝ)) ^ (1 : ℝ) = 1 / 3 by norm_num] at h2
        have : 2 / (3 : ℝ) + 1 / (3 : ℝ) = 1 := by norm_num
        linarith
      · have h1 : (2 / (3 : ℝ)) ^ t < (2 / (3 : ℝ)) ^ (1 : ℝ) := by
          apply (Real.rpow_lt_rpow_left_iff_of_base_lt_one ?_ ?_).mpr
          assumption
          all_goals norm_num
        have h2 : (1 / (3 : ℝ)) ^ t < (1 / (3 : ℝ)) ^ (1 : ℝ) := by
          apply (Real.rpow_lt_rpow_left_iff_of_base_lt_one ?_ ?_).mpr
          assumption
          all_goals norm_num
        rw [show (2 / (3 : ℝ)) ^ (1 : ℝ) = 2 / 3 by norm_num] at h1
        rw [show (1 / (3 : ℝ)) ^ (1 : ℝ) = 1 / 3 by norm_num] at h2
        have : 2 / (3 : ℝ) + 1 / (3 : ℝ) = 1 := by norm_num
        linarith
