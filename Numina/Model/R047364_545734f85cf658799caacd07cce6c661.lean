import Mathlib

theorem number_theory_93253 :
    IsGreatest {k : ℕ | 3 ^ k ∣ ∏ i ∈ Finset.range 100, (2 * i + 1)} 49 := by
  constructor
  · -- Show that 49 is in the set
    native_decide
  · -- Show that 49 is greatest
    intro k hk
    have h : 3 ^ k ∣ ∏ i in Finset.range 100, (2 * i + 1) := hk
    by_contra h'
    push_neg at h'
    have h2 : k ≥ 50 := by omega
    have h3 : ¬ (3 ^ 50 ∣ ∏ i in Finset.range 100, (2 * i + 1)) := by 
      native_decide
    have h4 : k ≥ 50 := by omega
    have h5 : 3 ^ 50 ∣ ∏ i in Finset.range 100, (2 * i + 1) := by
      have h5 : 3 ^ k ∣ ∏ i in Finset.range 100, (2 * i + 1) := h
      have h6 : k ≥ 50 := by omega
      have h7 : 3 ^ 50 ∣ 3 ^ k := by
        apply pow_dvd_pow _ (by omega)
      have h8 : 3 ^ 50 ∣ ∏ i in Finset.range 100, (2 * i + 1) := by 
        exact dvd_trans h7 h5
      exact h8
    have h4 : ¬ (3 ^ 50 ∣ ∏ i in Finset.range 100, (2 * i + 1)) := h3
    apply h4 at h5
    all_goals tauto