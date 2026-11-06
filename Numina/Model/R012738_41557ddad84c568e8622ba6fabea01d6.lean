import Mathlib

theorem number_theory_127411 (d : ℕ) (hd : d > 1) (r : ℕ)
    (hr : r = 1059 % d ∧ r = 1417 % d ∧ r = 2312 % d) :
    d - r = 15 := by
  rcases hr with ⟨h1, h2, h3⟩
  have h4 : 1059 % d = 1417 % d := by
    omega
  have h5 : 1417 % d = 2312 % d := by
    omega
  have h6 : d ∣ 358 := by
    have h : (1417 : ℕ) % d = (1059 : ℕ) % d := by
      omega
    have : d ∣ (1417 : ℕ) - (1059 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
    have : d ∣ (358 : ℕ) := by
      norm_num at this ⊢
      omega
    assumption
  have h7 : d ∣ 895 := by
    have h : (2312 : ℕ) % d = (1417 : ℕ) % d := by
      omega
    have : d ∣ (2312 : ℕ) - (1417 : ℕ) := by
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq h)
    have : d ∣ (895 : ℕ) := by
      norm_num at this ⊢
      omega
    assumption
  have h8 : d = 179 := by
    have h9 : d ∣ 179 := by
      exact Nat.dvd_gcd h6 h7
    have h11 : d ∣ 179 := h9
    have h12 : d ≤ 179 := by
      exact Nat.le_of_dvd (by linarith) h11
    interval_cases d <;> norm_num at h11 ⊢
    <;> try tauto
  have h9 : r = 164 := by
    rw [h8] at h1
    omega
  calc
    d - r = 179 - 164 := by
      rw [h8, h9]
    _ = 15 := by
      omega