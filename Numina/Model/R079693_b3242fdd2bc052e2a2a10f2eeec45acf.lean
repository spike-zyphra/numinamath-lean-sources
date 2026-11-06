import Mathlib

open Nat

theorem number_theory_4857 :
    IsGreatest {k | 0 < k ∧ (2 ^ k : ℤ) ∣ (2023 ! : ℤ)} 2014 := by 
  constructor
  · -- Show that 2014 is in the set.
    constructor
    · -- Show that 2014 is positive
      norm_num
    · -- Show that $2^{2014}$ divides $2023!$
      native_decide
  · -- Show that for all k in the set, k ≤ 2014
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    -- Now, we need to show that k ≤ 2014
    by_contra h
    push_neg at h
    -- Let's turn the division lemma 
    have h1 : k ≥ 2015 := by omega
    have h2 : ¬ (2 ^ 2015 : ℤ) ∣ (2023 ! : ℤ) := by native_decide
    have h3 : (2 : ℤ) ^ k ∣ (2023 ! : ℤ) := hk_div
    have h4 : (2 : ℤ) ^ 2015 ∣ (2 ^ k : ℤ) := by
      have : (2015 : ℕ) ≤ k := by omega
      exact pow_dvd_pow _ (show 2015 ≤ k by omega)
    have h5 : (2 : ℤ) ^ 2015 ∣ (2023 ! : ℤ) := by
      apply dvd_trans h4 h3
    contradiction