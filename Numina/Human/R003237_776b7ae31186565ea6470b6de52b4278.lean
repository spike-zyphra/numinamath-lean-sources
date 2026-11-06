import Mathlib

open Real

/- 15. [9] Find all real numbers $x$ between 0 and 360 such that $\sqrt{3} \cos 10^{\circ}=\cos 40^{\circ}+\sin x^{\circ}$. -/
theorem algebra_162953 (x : ℝ) (hx : x ∈ Set.Ioo 0 360) :
    Real.sqrt 3 * Real.cos (Real.pi / 18) = Real.cos (2 * Real.pi / 9) + Real.sin (x * Real.pi / 180) ↔
    x = 70 ∨ x = 110 := by
  -- Rewrite √3 as a cosine
  rw [show sqrt 3 = 2 * cos (π / 6) by simp; linarith]
  -- Rewrite arguments of cosine
  rw [show π / 6 = (2 * π / 9 + π / 9) / 2 by linarith, show π / 18 = (2 * π / 9 - π / 9) / 2 by linarith]
  -- Use cosine addition formula in reverse
  rw [← cos_add_cos]
  -- Cancel a term
  rw [add_right_inj]
  -- Convert cos to sin
  rw [← sin_pi_div_two_sub, show π / 2 - π / 9 = 7 * π / 18 by linarith, sin_eq_sin_iff]
  constructor
  · -- Prove that if the condition holds, then x is 70 or 110
    rintro ⟨k, hk⟩
    have lhs_pos : 0 < x * π / 180 := by simp at hx; nlinarith [pi_pos]
    have lhs_small : x * π / 180 < 2 * π := by simp at hx; nlinarith [pi_pos]
    rcases hk with h | h
    · -- Assume the first condition is true
      left
      -- We must have k = 0 by bounding
      have key : k = 0 := by
        -- Use contradiction
        by_contra hk
        rw [h] at lhs_small
        rw [h] at lhs_pos
        -- Do casework on if k is negative or positive
        apply lt_or_gt_of_ne at hk
        rcases hk with k_neg | k_pos
        · -- k is negative
          contrapose! lhs_pos
          rw [mul_comm, mul_comm 7, mul_div_assoc, ← mul_add, mul_nonpos_iff]
          left
          have : k ≤ -1 := by linarith
          rify at this
          refine ⟨pi_nonneg, ?_⟩
          calc
            (2 : ℝ) * k + 7 / 18 ≤ 2 * (-1 : ℤ) + 7 / 18 := by linarith [this]
            _ ≤ 0 := by norm_num
        -- k is positive
        have : k ≥ 1 := by linarith
        rify at this
        have lhs_big : _ :=
          calc
            2 * k * π + 7 * π / 18 ≥ 2 * π + 7 * π / 18 := by nlinarith [this]
            _ ≥ 2 * π := by linarith [pi_pos]
        -- We derive a contradiction
        rw [ge_iff_le, ← not_lt] at lhs_big
        tauto
      subst k
      nlinarith
    -- Assume the second condition is true
    right
    -- Show k is 0 by bounding
    have key : k = 0 :=by
      -- Use contradiction
      by_contra hk
      rw [h] at lhs_small
      rw [h] at lhs_pos
      -- Do casework on if k is negative or positive
      apply lt_or_gt_of_ne at hk
      rcases hk with k_neg | k_pos
      · have : k ≤ -1 := by linarith
        rify at this
        have : _ :=
          calc
            (2 * k + 1) * π - 7 * π / 18 ≤ -1 * π - 7 * π / 18 := by nlinarith
            _ < 0 := by nlinarith
        linarith
      have : 1 ≤ k := by linarith
      rify at this
      have : _ :=
        calc
          (2 * k + 1) * π - 7 * π / 18 ≥ 3 * π - 7 * π / 18 := by nlinarith
          _ > 2 * π := by nlinarith
      linarith
    subst k
    nlinarith
  -- Prove that 70 or 110 work
  intro h
  rcases h with rfl | rfl
  · -- Show that 70 is a valid solution
    use 0
    left
    linarith
  -- Show that 110 is a valid solution
  use 0
  right
  linarith