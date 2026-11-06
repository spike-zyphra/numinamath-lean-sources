import Mathlib
theorem number_theory_611265 : IsGreatest {n : ℕ | 2 ^ n ∣ 3 ^ 512 - 1} 11:= by 
  constructor
  · -- Show 11 is in the set
    native_decide
  · -- Show greatest
    intro n hn
    have h : 2 ^ n ∣ 3 ^ 512 - 1 := hn
    have h11 : n ≤ 11 := by 
      by_contra h2
      push_neg at h2
      have h2' : n ≥ 12 := by 
        omega
      have h3 : 2 ^ 12 ∣ 3 ^ 512 - 1 := by
        have h4 : 2 ^ n ∣ 3 ^ 512 - 1 := h
        have h5 : 2 ^ 12 ∣ 2 ^ n := by 
          apply pow_dvd_pow _ (by omega)
        have h6 : 2 ^ 12 ∣ 3 ^ 512 - 1 := by 
          exact dvd_trans h5 h4
        exact h6
      have h' : ¬ (2 ^ 12 ∣ 3 ^ 512 - 1) := by
        norm_num
      exact h' h3
    linarith