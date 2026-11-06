import Mathlib

theorem number_theory_210591 : IsGreatest {n | 3^n ∣ 4^27000 - 82} 5 := by
  constructor
  · -- Show 5 is in the set
    native_decide
  · -- Show that for all n in the set, n ≤ 5
    intro n hn
    have h5 : 3^n ∣ 4^27000 - 82 := hn
    by_contra h6
    push_neg at h6
    have h7 : n ≥ 6 := by omega
    have h8 : 3 ^ 6 ∣ (4 ^ 27000 - 82) := by
      have h9 : 3 ^ 6 ∣ 3 ^ n := by
        apply pow_dvd_pow _ (by omega)
      have h10 : 3 ^ n ∣ (4 ^ 27000 - 82) := h5
      have h11 : 3 ^ 6 ∣ (4 ^ 27000 - 82) := by
        exact dvd_trans h9 h10
      exact h11
    have h9 : ¬ (3 ^ 6 ∣ (4 ^ 27000 - 82)) := by
      native_decide
    exact h9 h8