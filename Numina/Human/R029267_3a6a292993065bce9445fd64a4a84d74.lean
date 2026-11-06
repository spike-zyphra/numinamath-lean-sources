import Mathlib

open Real Set

/- Determine the set of all possible values of $a$ such that the equation $|x| + 5a = ax - 1$ has two real roots. -/
theorem algebra_6154 (a : ℝ) : (∃ x y : ℝ, x ≠ y ∧ |x| + 5 * a = a * x - 1 ∧
    |y| + 5 * a = a * y - 1) ↔ a ∈ Ioo (-1) (-1 / 5) := by
  constructor
  -- Extend the existential assumption with $x$ and $y$, assume w. l. o. g. that $y$ is less than $x$
  · rintro ⟨x, y, ⟨xney, hx, hy⟩⟩; wlog yltx : y < x
    · push_neg at yltx; symm at xney
      exact this a y x xney hy hx (by rw [lt_iff_le_and_ne]; exact ⟨yltx, Ne.symm xney⟩)
  -- When $x$ is nonnegative, prove the statement is true
    by_cases h : 0 ≤ x
    -- Remove the absolute value in `hx` and solve for $x$
    · rw [abs_eq_self.mpr, eq_sub_iff_add_eq] at hx
      rw [add_assoc, ← eq_sub_iff_add_eq'] at hx
    -- Exclude the possibility that $a=1$
      rw [← sub_one_mul] at hx; by_cases ha : a = 1
      · simp [ha] at hx; linarith only [hx]
    -- Prove that $y$ is nonpositive
      have yneg : y ≤ 0 := by
        by_contra!; rw [abs_eq_self.mpr, eq_sub_iff_add_eq] at hy
        rw [add_assoc, ← eq_sub_iff_add_eq'] at hy
        rw [← sub_one_mul, hx] at hy; apply mul_left_cancel₀ at hy
        contradiction; rw [sub_ne_zero, ne_eq]; exact ha
        linarith only [this]
    -- Remove the absolute value in `hy` and solve for $y$
      rw [abs_eq_neg_self.mpr yneg, neg_add_eq_sub] at hy
      rw [sub_eq_sub_iff_add_eq_add, ← add_one_mul] at hy
    -- Exclude the possibility that $a=-1$
      by_cases h'a : a = -1
      · simp [h'a] at hy; linarith only [hy]
      nth_rw 2 [mul_comm] at hx hy; rw [← div_eq_iff] at hx hy
    -- Substitute $x$ and $y$ in `h` and `yneg`
      rw [← hx, div_nonneg_iff] at h; rw [← hy, div_nonpos_iff] at yneg
    -- Discuss all possible bounds on $a$ and use `linarith` tactics to finish the goal
      simp; rcases h with ⟨hl, hr⟩|⟨hl, hr⟩ <;> rcases yneg with ⟨h'l, h'r⟩|⟨h'l, h'r⟩
      any_goals constructor
      any_goals linarith
      · rw [lt_iff_le_and_ne]
        exact ⟨by linarith only [h'r], by intro h; simp [h] at h'a⟩
      · rw [lt_iff_le_and_ne]; constructor
        · linarith only [h'l]
        intro h; rw [h] at hx hy; norm_num at hx hy
        simp [← hx, ← hy] at xney
      · revert h'a; contrapose!; intro h; linarith only [h]
      revert ha; contrapose!; intro h; linarith only [h]
  -- When $x$ is negative, $y$ is also negative, we can remove the absolute values in `hx` and `hy`
    rw [abs_eq_neg_self.mpr] at hx hy
    apply_fun fun t => t - (a * y - 1) at hx
    nth_rw 1 [← hy, ← sub_eq_zero] at hx; ring_nf at hx
    simp [show -x - x * a + a * y + y = (a + 1) * (y - x) by ring] at hx
  -- Show that $a=-1$ or $y-x=0$, but both quickly lead to contradiction from `linarith` tactics
    rcases hx with h|h
    · replace h : a = -1 := by linarith only [h]
      rw [← sub_eq_zero, h] at hy; ring_nf at hy
      linarith only [hy]
    all_goals linarith only [h, yltx]
-- Conversely, when $x$ is in $(-1,-1/5)$, we can get two different solutions $(5 * a + 1) / (a - 1)$ and $(5 * a + 1) / (a + 1)$
  rintro ⟨agt, alt⟩; use (5 * a + 1) / (a - 1), (5 * a + 1) / (a + 1); split_ands
  · intro h; rw [div_eq_div_iff] at h
    apply mul_left_cancel₀ at h; linarith only [h]
    any_goals linarith only [alt]
    linarith only [agt]
  · rw [abs_eq_self.mpr]
    field_simp [show a - 1 ≠ 0 by linarith only [alt]]; ring
    apply div_nonneg_of_nonpos; all_goals linarith
  rw [abs_eq_neg_self.mpr]
  field_simp [show a + 1 ≠ 0 by linarith only [agt]]; ring
  apply div_nonpos_of_nonpos_of_nonneg; all_goals linarith
