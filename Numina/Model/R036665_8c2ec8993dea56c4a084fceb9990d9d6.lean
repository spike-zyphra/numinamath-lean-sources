import Mathlib

open Real
open scoped BigOperators

theorem number_theory_322114 :
  IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} (10 + 9 / 19) := by
  constructor
  · -- Show that 10 + 9 / 19 is in the set.
    use 199
    constructor
    · -- Show that 199 is in the range [100, 999].
      native_decide
    · -- Show that the quotient equals 10 + 9 / 19.
      norm_num
  · -- Show that 10 + 9 / 19 is the smallest in the set.
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨h100, h999⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 100 := by linarith
    have h2 : n ≤ 999 := by linarith
    interval_cases n <;> norm_num [hx] at h ⊢ <;> norm_num at h ⊢