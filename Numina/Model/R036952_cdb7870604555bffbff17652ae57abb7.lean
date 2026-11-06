import Mathlib

theorem number_theory_278174 : IsGreatest {n | ∃ k : ℕ, ∏ i ∈ Finset.Icc 810 2010, i = k * 810^n} 150 := by
  constructor
  · -- Show that 150 is in the set
    use (∏ i ∈ Finset.Icc 810 2010, i) / (810 ^ 150)
    native_decide
  · -- Show that 150 is the greatest
    intro n hn
    rcases hn with ⟨k, hk⟩
    by_contra h
    push_neg at h
    have h2 : n > 150 := by linarith
    have h3 : k * 810 ^ n ∣ ∏ i ∈ Finset.Icc 810 2010, i := by 
      rw [hk]
      all_goals omega
    have h4 : 810 ^ n ∣ ∏ i ∈ Finset.Icc 810 2010, i := by 
      exact dvd_trans (dvd_mul_left (810 ^ n) k) h3
    have h5 : 810 ^ 151 ∣ ∏ i ∈ Finset.Icc 810 2010, i := by
      have h6 : n ≥ 151 := by omega
      have h7 : 810 ^ 151 ∣ 810 ^ n := by 
        exact pow_dvd_pow _ (by omega)
      exact dvd_trans h7 h4
    have h6 : ¬(810 ^ 151 ∣ ∏ i ∈ Finset.Icc 810 2010, i) := by
      native_decide
    exact h6 h5