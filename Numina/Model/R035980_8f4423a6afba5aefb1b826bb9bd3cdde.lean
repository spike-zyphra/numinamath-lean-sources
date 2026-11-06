import Mathlib

theorem number_theory_116653 (d : ℕ) (hd : d > 1) (r : ℕ)
    (hr : r = 1059 % d ∧ r = 1417 % d ∧ r = 2312 % d) :
    d - r = 15 := by 
  rcases hr with ⟨hr1, hr2, hr3⟩
  have h4 : 1059 % d = 1417 % d := by 
    omega 
  have h5 : 1417 % d = 2312 % d := by 
    omega 
  have h6 : (d) ∣ 358 := by
    have h7 : (1059 : ℕ) % d = (1417 : ℕ) % d := h4
    have h8 : d ∣ (1417 - 1059) := by
      have h9 : (1417 % d) = (1059 % d) := by 
        omega 
      have h10 : d ∣ (1417 - 1059) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h9)
      exact h10 
    have h9 : (1417 - 1059 : ℕ) = 358 := by 
      omega 
    rw [h9] at h8
    exact h8 
  have h8' : (d) ∣ 895 := by
    have h7 : (1417 : ℕ) % d = (2312 : ℕ) % d := h5
    have h9 : d ∣ (2312 - 1417) := by
      have h10 : (2312 % d) = (1417 % d) := by
        omega 
      have h11 : d ∣ (2312 - 1417) := by
        exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h10)
      exact h11 
    have h9' : (2312 - 1417 : ℕ) = 895 := by
      omega 
    rw [h9'] at h9
    exact h9 
  have h10 : (d) ∣ 179 := by 
    exact Nat.dvd_gcd h6 h8' 
  have h11 : (d) = 179 := by
    have h12 : (d) ∣ 179 := h10
    have h13 : d ≤ 179 := by 
      exact Nat.le_of_dvd (by norm_num) h12
    interval_cases d <;> norm_num at h12 ⊢ <;> try tauto 
  have hr179 : r = 164 := by
    rw [show d = 179 by omega] at hr1
    have : r = 1059 % 179 := by
      linarith [hr1]
    norm_num at this ⊢
    omega 
  calc
    d - r = 179 - 164 := by rw [h11, hr179]
    _ = 15 := by omega