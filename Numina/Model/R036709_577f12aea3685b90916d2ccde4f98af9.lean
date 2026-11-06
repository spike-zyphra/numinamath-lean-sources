import Mathlib

open Finset

theorem number_theory_79623 : IsGreatest {n : ℕ | 2 ^ n ∣ ∏ i ∈ range 64, Nat.choose (2 * i + 2) (i + 1)} 193 := by 
  constructor
  · -- First part: prove 193 is in the set
    native_decide
  · -- Second part: prove no larger integer is in the set
    intro n hn
    have h : 2 ^ n ∣ ∏ i ∈ range 64, Nat.choose (2 * i + 2) (i + 1) := hn
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 194 := by omega
    have h3 : ¬ (2 ^ 194 ∣ ∏ i ∈ range 64, Nat.choose (2 * i + 2) (i + 1)) := by
      native_decide
    have h4 : 2 ^ 194 ∣ 2 ^ n := by
      apply pow_dvd_pow _ (by omega)
    have h5 : 2 ^ 194 ∣ ∏ i ∈ range 64, Nat.choose (2 * i + 2) (i + 1) := by
      exact dvd_trans h4 h
    have h6 : ¬ (2 ^ 194 ∣ ∏ i ∈ range 64, Nat.choose (2 * i + 2) (i + 1)) := h3
    contradiction