import Mathlib

open Nat BigOperators

theorem number_theory_1354 :
    IsGreatest {n | ¬(3^6 ∣ (n)!)} 14 := by
  constructor
  · -- Show that 14 is in the set
    native_decide
  · -- Show that for all n in the set, n ≤ 14
    intro n hn
    have h : ¬(3^6 ∣ (n)!) := by
      simpa using hn
    by_contra h'
    push_neg at h'
    have h15 : n ≥ 15 := by omega
    have h2 : (3 ^ 6 ∣ (n)!) := by
      have h9 : ∀ n : ℕ, n ≥ 15 → 3 ^ 6 ∣ (n)! := by
        intro n hn
        have base := show 3 ^ 6 ∣ (15)! by native_decide
        have step : ∀ k : ℕ, k ≥ 15 → 3 ^ 6 ∣ (k)! → 3 ^ 6 ∣ (k + 1)! := by
          intros k hk h
          have h10 : (k + 1)! = (k + 1) * (k)! := by simp [Nat.factorial]
          rw [h10]
          exact dvd_mul_of_dvd_right h (k + 1)
        exact Nat.le_induction base step n hn
      specialize h9 n h15
      simpa using h9
    have h4 : ¬(3^6 ∣ (n)!) := h
    contradiction