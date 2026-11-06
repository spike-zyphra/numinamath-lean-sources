import Mathlib

theorem number_theory_165527 : IsGreatest {n | 3^n ∣ ∏ i ∈ Finset.Icc 1 2020, i} 1005 := by 
  constructor
  · -- Show that 1005 is in the set.
    native_decide
  · -- Show that 1005 is greatest element.
    intro n hn
    have h2n : 3 ^ n ∣ ∏ i ∈ Finset.Icc 1 2020, i := hn
    -- We need to relate 3^n ∣ n! to the product
    have h3n1 : ¬(3 ^ 1006 ∣ Nat.factorial 2020) := by
      native_decide
    by_contra h
    push_neg at h
    -- Assume n > 1005, derive contradiction
    have h4 : n > 1005 := h
    have h5 : 3 ^ 1006 ∣ 3 ^ n := by
      apply pow_dvd_pow _ (by linarith)
    have h3n : 3 ^ 1006 ∣ ∏ i ∈ Finset.Icc 1 2020, i := by
      have h6 : 3 ^ 1006 ∣ 3 ^ n := h5
      have h7 : 3 ^ n ∣ ∏ i ∈ Finset.Icc 1 2020, i := h2n
      have h8 : 3 ^ 1006 ∣ ∏ i ∈ Finset.Icc 1 2020, i := by
        have h9 : 3 ^ 1006 ∣ 3 ^ n := h6
        have h10 : 3 ^ n ∣ ∏ i ∈ Finset.Icc 1 2020, i := h7
        exact dvd_trans h9 h10
      exact h8
    have h7 : 3 ^ 1006 ∣ Nat.factorial 2020 := by
      have h8 : ∏ i in Finset.Icc 1 2020, i = Nat.factorial 2020 := by
        native_decide
      rw [show ∏ i in Finset.Icc 1 2020, i = Nat.factorial 2020 by native_decide] at h3n
      tauto
    contradiction