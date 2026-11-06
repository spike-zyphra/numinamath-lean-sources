import Mathlib

theorem number_theory_4779 (a b : ℤ) (q r : ℤ) (hb : 0 < b) (ha : a = b * q + r) (hr : 0 ≤ r ∧ r < b) :
    if b ∣ a then (-a)/b = -q ∧ (-a)%b = 0
    else (-a)/b = -(q + 1) ∧ (-a)%b = b - r := by
  have : r+b*q=a ∧ 0 ≤ r ∧ r <b := by
    split_ands
    . rw [ha]; ring
    . exact hr.1
    . exact hr.2
  rw [← Int.ediv_emod_unique hb] at this
  split
  -- b | a
  next hab =>
    constructor
    -- quotient is -q
    . rw [← this.1]; exact Int.neg_ediv_of_dvd hab
    -- remainder is 0
    . apply Int.emod_eq_zero_of_dvd
      exact Int.dvd_neg.mpr hab
  -- b ∤ a
  next hab =>
    rw [Int.ediv_emod_unique hb]
    split_ands
    -- quotient is -(q+1)
    conv_rhs => rw [ha]
    ring
    -- ensure the two side equal
    all_goals omega