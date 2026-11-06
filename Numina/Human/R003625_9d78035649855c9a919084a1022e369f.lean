import Mathlib

open Real

/- 13. Prove: The equation $(x+1)^{\log _{3} 2}=x$ has a unique positive real solution. -/
theorem algebra_202551 : ∃! (x : ℝ), 0 < x ∧ (x + 1) ^ logb 3 2 = x := by
  -- we convert the goal to following which is easier to prove
  suffices ∃! (t : ℝ) , (3 ^ t : ℝ) = 2 ^ t + 1 by
    obtain ⟨t, ht1, ht2⟩ := this
    -- in particular t ≠ 0
    have : t ≠ 0 := by
      by_contra ht
      rw [ht] at ht1
      norm_num at ht1
    -- show that x = 3^t - 1 will be the unique solution
    use 3 ^ t - 1
    and_intros
    -- inequaliity is easy to prove
    . rw [ht1]
      simp
      apply rpow_pos_of_pos (by norm_num)
    --  then we prove it is a solution
    . nth_rw 2 [ht1]
      simp
      rw [← logb_eq_iff_rpow_eq]
      -- goal is now logb (3 ^ t) (2 ^ t) = logb 3 2 and the conditions for logb_eq_iff_rpow_eq
      any_goals (apply rpow_pos_of_pos (by norm_num))
      . rw [logb, logb, log_rpow (by norm_num), log_rpow (by norm_num)]
        field_simp
        ring
      -- to prove 3^t ≠ 1, we have to use monotoneness of 3^x, to prove t must be 0 if 3^t = 1
      . simp
        by_contra h
        rw [show (1 : ℝ) = 3 ^ (0 : ℝ) by norm_num] at h
        have : StrictMono fun (x : ℝ) ↦ ((3 : ℝ) ^ x) := by
          apply strictMono_rpow_of_base_gt_one (by norm_num)
        have := (StrictMono.injective this)  h
        contradiction
    -- next to prove uniqueness, assume there is a y that satisfies the condition
    . simp
      rintro y hy1 hy2
      specialize ht2 (logb 3 (y + 1))
      -- y = 3^t - 1 can be converted to logb 3 (y + 1) = t
      rw [eq_sub_iff_add_eq', add_comm, eq_comm]
      apply logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith) |>.mp
      -- we will use uniquess of t
      apply ht2
      -- now goal is 3 ^ logb 3 (y + 1) = 2 ^ logb 3 (y + 1) + 1, simplify lhs
      rw [rpow_logb (by norm_num) (by norm_num) (by linarith)]
      congr
      -- goal is y = 2 ^ logb 3 (y + 1), now just convert all terms to logs and field_simp on goal and on hy2
      rw [eq_comm, ← logb_eq_iff_rpow_eq (by norm_num) (by norm_num) (by linarith), logb, logb]
      field_simp
      rw [← logb_eq_iff_rpow_eq (by linarith) (by linarith) (by assumption), logb, logb] at hy2
      have : log (y + 1) ≠ 0 := by
        apply log_ne_zero_of_pos_of_ne_one (by linarith) (by linarith)
      field_simp at hy2
      linarith
  -- now we'll show unique t is 1
  use 1
  -- condition is easily computed, we just need to prove unqiueness
  norm_num
  -- assume y is another value for t
  rintro y hy
  -- first y ≠ 0 as before
  have : y ≠ 0 := by
    by_contra h
    rw [h] at hy
    norm_num at hy
  -- convert the condition to 1 = (3 ^ y)⁻¹ + (2 / 3) ^ y
  replace hy := congrArg (· / ((3 : ℝ) ^y)) hy
  ring_nf at hy
  have : (3 ^ y) * (3 ^ y)⁻¹ = (1 : ℝ) := by
    apply GroupWithZero.mul_inv_cancel
    apply rpow_ne_zero (by norm_num) (by assumption) |>.mpr (by norm_num)
  rw [this] at hy
  have : (3 ^ y)⁻¹ * 2 ^ y = (2 / 3 : ℝ) ^ y := by
    rw [div_rpow (by norm_num) (by norm_num)]
    ring
  rw [this] at hy
  -- now we'll show following f is antitone, hence injective
  let f (x : ℝ) := ((1 / 3) ^ x + (2 / 3) ^ x : ℝ)
  have hf : Function.Injective f := by
    apply StrictAnti.injective
    apply StrictAnti.add
    . apply strictAnti_rpow_of_base_lt_one <;> norm_num
    . apply strictAnti_rpow_of_base_lt_one <;> norm_num
  -- so f 0 = f t is enough to prove the goal, norm_num and manipulate to show that is true.
  apply hf
  simp [f]
  norm_num
  nth_rw 2 [hy]
  simp
  apply inv_rpow (by norm_num)