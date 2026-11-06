import Mathlib

open Real
open scoped BigOperators

theorem inequalities_199502 :
  IsLeast {x : ℕ | ∑ i in Finset.range 2001, (2 : ℕ)^(x + i) > 2^2017} 17 := by
  constructor
  · -- Show 17 is in the set
    native_decide
  · -- Show no natural smaller than 17 is in the set
    intro y hy
    have h : ∑ i in Finset.range 2001, (2 : ℕ)^(y + i) > 2^2017 := hy
    by_contra h'
    push_neg at h'
    have h1 : y ≤ 16 := by omega
    have h2 : ∑ i in Finset.range 2001, (2 : ℕ)^(y + i) ≤ 2^2017 := by
      interval_cases y <;> native_decide
    linarith