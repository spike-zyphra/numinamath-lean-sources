import Mathlib

open Real Set
open scoped Real

/- Show that if $\alpha, \beta$, and $\gamma$ are the angles of a triangle, then


$$

(\sin \alpha+\sin \beta+\sin \gamma)^{2}>9 \sin \alpha \sin \beta \sin \gamma

$$
 -/
theorem inequalities_213857 (α β γ : Real) (h : α ∈ Ioo 0 π)
    (h' : β ∈ Ioo 0 π) (h'' : γ ∈ Ioo 0 π) (h''' : α + β + γ = π) :
    (sin α + sin β + sin γ)^2 > 9 * sin α * sin β * sin γ := by

  -- first we simplify to get rid of the `Ioo` in hypotheses
  simp at *

  -- weights for AM-GM inequality (all equal to `1 / 3`)
  set weights: ℕ → ℝ := fun _ => (1: ℝ) / 3

  -- proofs that all weights are nonneg and they sum to `1`
  have all_weights_are_nonneg i (Hi: i ∈ Finset.range 3): 0 ≤ weights i := by
    simp [weights]
  have sum_of_weights_is_one: ∑ (i ∈ Finset.range 3), weights i = 1 := by
    simp [weights]

  -- values for AM-GM inequality (values of sine of all three angles)
  set sine_of_angles: ℕ → ℝ :=
    fun n => match n with
    | 0 => sin α
    | 1 => sin β
    | _ => sin γ

  -- proof that for all three angles values of sine are positive
  have all_sine_are_positive i (Hi: i ∈ Finset.range 3): 0 < sine_of_angles i := by
    simp at Hi
    interval_cases i <;> simp [sine_of_angles]
    . exact sin_pos_of_mem_Ioo h
    . exact sin_pos_of_mem_Ioo h'
    . exact sin_pos_of_mem_Ioo h''

  -- proof that for all three angles values of sine are nonneg
  -- (uses previous result just above)
  have all_sine_are_nonneg i (Hi: i ∈ Finset.range 3): 0 ≤ sine_of_angles i := by
    simp at Hi
    interval_cases i <;> simp [sine_of_angles]
    . have H := all_sine_are_positive 0 (by simp)
      exact le_of_lt H
    . have H := all_sine_are_positive 1 (by simp)
      exact le_of_lt H
    . have H := all_sine_are_positive 2 (by simp)
      exact le_of_lt H

  -- now we are ready to use AM-GM inequality
  have AMGM_instance :=
    geom_mean_le_arith_mean_weighted (Finset.range 3)
    weights sine_of_angles all_weights_are_nonneg sum_of_weights_is_one all_sine_are_nonneg

  -- lemma that changes the sum in AM-GM inequality to explicit expression
  have AM_simp: ∑ i ∈ Finset.range 3, weights i * sine_of_angles i = (sin α + sin β + sin γ) / 3 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [weights, sine_of_angles]
    linarith

  -- different inequalities that are useful later
  have H1: 0 < sin α := by exact (all_sine_are_positive 0 (by simp))
  have H2: 0 < sin β := by exact (all_sine_are_positive 1 (by simp))
  have H3: 0 < sin γ := by exact (all_sine_are_positive 2 (by simp))
  have H5: 0 ≤ sin α + sin β + sin γ := by linarith
  have H6: 0 ≤ sin α * sin β * sin γ := Left.mul_nonneg (Left.mul_nonneg (le_of_lt H1) (le_of_lt H2)) (le_of_lt H3)
  have H7: 0 ≤ (sin α * sin β * sin γ) ^ ((1: ℝ) / 3) := rpow_nonneg H6 (1 / 3)

  -- lamma that changes the product in AM-GM inequality to explicit expression
  have GM_simp: ∏ i ∈ Finset.range 3, sine_of_angles i ^ weights i = (sin α * sin β * sin γ) ^ ((1: ℝ) / 3) := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
    simp [weights, sine_of_angles]
    rw [<- mul_rpow, <- mul_rpow]
    . refine Left.mul_nonneg (le_of_lt H1) (le_of_lt H2)
    . exact (le_of_lt H3)
    . exact (le_of_lt H1)
    . exact (le_of_lt H2)

  -- let's simplify our case of AM-GM inequality a bit
  rw [AM_simp, GM_simp] at AMGM_instance
  clear AM_simp GM_simp

  -- some transformations  of our AM-GM inequality follows
  have H8 (u w: ℝ) (Huw: u ≤ w / 3): u * 3 ≤ w := by linarith
  apply H8 at AMGM_instance

  rw [<- sq_le_sq₀ (Left.mul_nonneg H7 (by norm_num)) H5] at AMGM_instance

  rw [mul_pow _ _ 2, <- rpow_two, <- rpow_mul H6] at AMGM_instance
  norm_num at AMGM_instance


  -- now we prove that for `x` from interval `(0, π)`
  -- the sine is equal to `1` iff `x = π / 2`
  have H9 (x: ℝ) (Hx0: 0 < x) (Hx1: x < π): sin x = 1 ↔ x = π / 2 := by
    -- rewrite using library lemma
    rw [sin_eq_one_iff]
    constructor <;> intro H10
    . -- direction from let to right
      -- first we use information in `H10`
      obtain ⟨k, Hk⟩ := H10
      -- there are three cases to look at:
      -- 1) k < 0, which leads to contradiction
      -- 2) k = 0 (and we can prove the goal easy)
      -- 3) 0 < k, which leads to contradiction too
      obtain H11 | H11 | H11 := lt_trichotomy k 0
      . exfalso
        -- as it turns out, `k` is too much (below zero)
        -- and expression `π / 2 + ↑k * (2 * π)` can't be equal to `π / 2`
        have H12: k ≤ -1 := by linarith
        have H13: (k: ℝ) ≤ -1 := by norm_cast
        have H14: (k: ℝ) * (2 * π) ≤ - (2 * π) := by nlinarith [two_pi_pos]
        linarith
      . subst k
        simp at Hk
        tauto
      . exfalso
        -- some idea as with negative `k`, but in positive directionS
        have H12: 1 ≤ k := by linarith
        have H13: 1 ≤ (k: ℝ) := by norm_cast
        have H14: 2 * π ≤ (k: ℝ) * (2 * π) := by nlinarith [two_pi_pos]
        linarith
    . subst x
      simp

  -- tedious proof that product of all three sine values is less than 1
  have H10: sin α * sin β * sin γ < 1 := by
    -- of course, sine is bounded above by `1`
    -- (for all three angles)
    have H11: sin α ≤ 1 := by exact sin_le_one α
    have H12: sin β ≤ 1 := by exact sin_le_one β
    have H13: sin γ ≤ 1 := by exact sin_le_one γ
    -- we take a look at the eight possible cases:
    -- they happen because we look at
    -- fact that `sin α = 1` or `sin α ≠ 1` and
    -- and the same thing with other two angles
    obtain H14 | H14 := em (sin α = 1) <;>
    obtain H15 | H15 := em (sin β = 1) <;>
    obtain H16 | H16 := em (sin γ = 1)
    . -- sum of our three angles can't exceed `π`,
      -- therefore contradiction, which is solved by `linarith`
      -- (with a hint about positivity of `π`)
      rw [H9 _ h.1 h.2] at H14
      rw [H9 _ h'.1 h'.2] at H15
      rw [H9 _ h''.1 h''.2] at H16
      linarith [pi_pos]
    . -- sum of angles can't exceed `pi`
      rw [H9 _ h.1 h.2] at H14
      rw [H9 _ h'.1 h'.2] at H15
      linarith [pi_pos]
    . -- sum of angles can't exceed `pi`
      rw [H9 _ h.1 h.2] at H14
      rw [H9 _ h''.1 h''.2] at H16
      linarith [pi_pos]
    . -- `sin α = 1`, but other sine values is less than `1`,
      -- so their product is less than `1`
      simp [H14]
      have H17: sin β < 1 := lt_of_le_of_ne H12 H15
      have H18: sin γ < 1 := lt_of_le_of_ne H13 H16
      exact Right.mul_lt_one_of_le_of_lt_of_nonneg H12 H18 (le_of_lt H3)
    . -- sum of angles can't exceed `pi`
      rw [H9 _ h'.1 h'.2] at H15
      rw [H9 _ h''.1 h''.2] at H16
      linarith
    . -- `sin β = 1`, but other sine values is less than `1`,
      -- so their product is less than `1`
      simp [H15]
      have H17: sin α < 1 := lt_of_le_of_ne H11 H14
      have H18: sin γ < 1 := lt_of_le_of_ne H13 H16
      exact Right.mul_lt_one_of_le_of_lt_of_nonneg H11 H18 (le_of_lt H3)
    . --`sin γ = 1`, but other sine values is less than `1`,
      -- so their product is less than `1`
      simp [H16]
      have H17: sin α < 1 := lt_of_le_of_ne H11 H14
      have H18: sin β < 1 := lt_of_le_of_ne H12 H15
      exact Right.mul_lt_one_of_le_of_lt_of_nonneg H11 H18 (le_of_lt H2)
    . -- all three sine values is less than `1`,
      -- so their product also is less than `1`
      have H17: sin α < 1 := lt_of_le_of_ne H11 H14
      have H18: sin β < 1 := lt_of_le_of_ne H12 H15
      have H19: sin γ < 1 := lt_of_le_of_ne H13 H16
      have H20: sin α * sin β < 1 := Right.mul_lt_one_of_le_of_lt_of_nonneg H11 H18 (le_of_lt H2)
      exact Right.mul_lt_one_of_lt_of_le_of_pos H20 H13 H3

  -- we prove tiny but useful inequality
  -- about powers of a number, if it is from interval `(0, 1)`
  have H11 (x: ℝ) (Hx0: 0 < x) (Hx1: x < 1): x ^ (1: ℝ) < x ^ ((2: ℝ) / 3) := by
    rw [Real.rpow_lt_rpow_left_iff_of_base_lt_one Hx0 Hx1]
    norm_num
  simp at H11

  -- we finish with proving that the product of sine values is positive,
  -- then using inequality `H11` on product of sine values,
  -- and finally using `linarith`
  have H12: 0 < sin α * sin β * sin γ := by
    have H13: 0 < sin α * sin β := by exact mul_pos H1 H2
    exact mul_pos H13 H3

  have H13 := H11 _ H12 H10

  linarith