import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

theorem number_theory_4882 : IsGreatest {n | 0 < n ∧ (2^n : ℕ) ∣ Nat.factorial 34} 32 := by
  constructor
  · -- Show 32 is in the set
    constructor
    · -- Show 32 > 0
      norm_num
    · -- Show 2^32 divides 34!
      native_decide
  · -- Show that there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n > 32 := by linarith
    -- Now prove that 2^n does not divide 34! if n > 32. Specifically, 2^33 does not divide 34!
    have h2 : ¬ (2^33 : ℕ) ∣ Nat.factorial 34 := by native_decide
    have h3 : (2^33 : ℕ) ∣ 2^n := by
      have h4 : 33 ≤ n := by omega
      exact pow_dvd_pow _ (by omega)
    have h6 : (2^33 : ℕ) ∣ Nat.factorial 34 := by
      exact Nat.dvd_trans h3 hn_div
    contradiction