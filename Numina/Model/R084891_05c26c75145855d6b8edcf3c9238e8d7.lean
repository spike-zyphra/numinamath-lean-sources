import Mathlib

theorem number_theory_308500 : IsGreatest {k | 0 < k ∧ (2010 ^ k : ℕ) ∣ ∏ i ∈ Finset.Icc 1 2011, i} 30 := by
  constructor
  · -- Show 30 is in the set
    native_decide
  · -- Show that k <= 30 for all k in the set
    intro k h
    rcases h with ⟨hk, hdiv⟩
    by_contra h2
    push_neg at h2
    have h2' : k > 30 := by linarith
    have h3 : k ≥ 31 := by omega
    have h4 : ¬ (2010 ^ 31 : ℕ) ∣ ∏ i ∈ Finset.Icc 1 2011, i := by
      native_decide
    have h5 : (2010 ^ 31 : ℕ) ∣ (2010 ^ k : ℕ) := by
      apply pow_dvd_pow _ (by omega)
    have h6 : (2010 ^ 31 : ℕ) ∣ ∏ i ∈ Finset.Icc 1 2011, i := by
      apply dvd_trans h5 hdiv
    contradiction