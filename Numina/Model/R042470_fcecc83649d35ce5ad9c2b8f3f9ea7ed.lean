import Mathlib

theorem number_theory_13991 :
    IsGreatest {k | 0 < k ∧ (3 ^ k : ℤ) ∣ ∏ i ∈ Finset.range 100, (2 * i + 1)} 49 := by
  constructor
  · -- Show 49 is in the set, i.e., 49 > 0 and 3^49 divides the product
    constructor
    · norm_num
    · native_decide
  · -- Show that if k is in the set, then k ≤ 49
    intro k hk
    rcases hk with ⟨hk1, hkd⟩
    by_contra h
    push_neg at h
    have h50 : k ≥ 50 := by omega
    have h6 : ¬ (3 ^ 50 : ℤ) ∣ ∏ i ∈ Finset.range 100, (2 * i + 1) := by
      native_decide
    have h7 : (3 ^ k : ℤ) ∣ ∏ i ∈ Finset.range 100, (2 * i + 1) := hkd
    have h8 : (3 ^ 50 : ℤ) ∣ (3 ^ k : ℤ) := by
      apply pow_dvd_pow _ (show 50 ≤ k by omega)
    have h9 : (3 ^ 50 : ℤ) ∣ ∏ i ∈ Finset.range 100, (2 * i + 1) := by
      exact dvd_trans h8 h7
    contradiction