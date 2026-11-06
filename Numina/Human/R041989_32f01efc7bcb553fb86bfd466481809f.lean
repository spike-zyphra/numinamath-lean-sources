import Mathlib

open Real Set
open scoped BigOperators

/- 4. Find all values of the parameter $a$, for each of which the equation $a|x+1|+\frac{x^{2}-5 x+6}{2-x}=0$ has exactly one solution -/
theorem algebra_144626 (a : ℝ) :
    (∃! x : ℝ, 2 - x ≠ 0 ∧ a * |x + 1| + (x ^ 2 - 5 * x + 6) / (2 - x) = 0) ↔
    a ∈ Ico (-1) (-1 / 3) ∪ Ioo (-1 / 3) 1 := by
  -- first of all, use the fact that 2 - x ≠ 0 to convert the division to one linear expression
  have (x : ℝ) : 2 - x ≠ 0 ∧ a * |x + 1| + (x ^ 2 - 5 * x + 6) / (2 - x) = 0 ↔ 2 - x ≠ 0 ∧ a * |x + 1| + 3 - x = 0 := by
    simp
    rintro h
    rw [show x ^ 2 - 5 * x + 6 = (3 - x) * (2 - x) by ring]
    field_simp
    ring_nf
  simp_rw [this]
  -- next also convert union of two interval to one interval with a hole, as it's easier to work that way
  have : a ∈ Ico (-1) (-1 / 3) ∪ Ioo (-1 / 3) 1 ↔ a ∈ Ico (-1) 1 ∧ a ≠ -1/3 := by
    simp; constructor <;> rintro h
    . obtain ⟨h1, h2⟩ | ⟨h1, h2⟩ := h
      all_goals and_intros <;> linarith
    . obtain ⟨⟨h1, h2⟩, h3⟩ := h
      obtain h4 | h4 := lt_or_gt_of_ne h3
      . left; and_intros <;> linarith
      . right; and_intros <;> linarith
  simp_rw [this]
  -- now we prove both implications
  constructor
  -- to prove unique solution implies the bounds, we prove the contrapositive
  . contrapose
    simp [-not_and, Decidable.not_and_iff_or_not_not', or_assoc]
    rintro h'
    -- there are 3 cases, x < -1, 1 ≤ x, x = -1/3
    obtain h' | h' | h' := h'
    -- first case, we prove there are multiple solution, in paritcular (a + 3) / (1 - a) and (a - 3) / (- a  - 1)
      -- in first solution, absolute value is positive of input
    . apply mt ExistsUnique.unique; simp
      use (a + 3) / (1 - a)
      have : 0 < 1 - a := by linarith
      rw [show (a + 3) / (1 - a) + 1 = 4 / (1 - a) by field_simp; ring]
      rw [abs_eq_self.mpr (div_pos (by norm_num) (by assumption)).le]
      field_simp; ring_nf; simp
      and_intros
      . linarith
        -- in second solution, absolute value is negative of input
      . use (a - 3) / (- a - 1)
        have : 0 < - a - 1 := by linarith
        rw [show 1 + (a - 3) / (-a - 1) = -4 / (-a - 1) by field_simp; ring]
        rw [abs_eq_neg_self.mpr (div_neg_of_neg_of_pos (by norm_num) (by assumption)).le]
        field_simp; ring_nf; simp
        and_intros
        -- and two solution are not equal as equality implies a = 0 or a = -1, both not possible
        . linarith
        . rintro ha
          have : a * (1 + a) = 0 := by linarith
          simp at this
          obtain ha' | ha' := this <;> linarith
    -- second case, we prove there are no solutions at all
    . apply mt ExistsUnique.exists
      simp; rintro x hx hx''
      -- we casework on positive abs and negative abs and in both cases, inequalities disprove the solution
      obtain hx''' | hx''' := LinearOrder.le_total (x + 1) 0
      . rw [abs_eq_neg_self.mpr (by assumption)] at hx''
        nlinarith
      . rw [abs_eq_self.mpr (by assumption)] at hx''
        nlinarith
    -- third case, we prove no solutions at all
    . rw [h']
      apply mt ExistsUnique.exists
      simp
      rintro x hx hx'
      -- again we do casework, but here one of the case basically puts x at the hole
      obtain hx'' | hx'' := LinearOrder.le_total (x + 1) 0
      . rw [abs_eq_neg_self.mpr (by assumption)] at hx'
        linarith
      . rw [abs_eq_self.mpr (by assumption)] at hx'
        rw [show x = 2 by linarith] at hx
        norm_num at hx
  -- now we prove opposite implication,
  . simp; rintro a_lb a_hb a_ne
    -- we show that the unique solutoin is (-3-a) / (a-1)
    use (- 3 - a) / (a - 1)
    simp
    have : a - 1 < 0 := by linarith
    have : a - 1 ≠ 0 := by linarith
    -- the absolute value expression is positive
    rw [show (- 3 - a) / (a - 1) + 1 = -4 / (a - 1) by field_simp; ring]
    have : 0 < -4 / (a - 1) := by
      apply div_pos_of_neg_of_neg
      . norm_num
      . assumption
    -- now we can prove the targtes via linarith and nlinarith
    rw [abs_eq_self.mpr (by linarith)]
    field_simp
    ring_nf
    simp
    and_intros
    . by_contra h
      have : a = - 1 / 3 := by linarith
      contradiction
    . rintro y hy hy'
      obtain hy'' | hy'' := LinearOrder.le_total (1 + y) 0
      . rw [abs_eq_neg_self.mpr (by assumption)] at hy'
        nlinarith
      . rw [abs_eq_self.mpr (by assumption)] at hy'
        linarith