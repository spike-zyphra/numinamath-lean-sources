import Mathlib

theorem number_theory_5882
    (a n t b : ℤ)
    (h₀ : a = 2 * t - 1) :
    (a ∣ 2 * n → a ∣ n) ∧ (2 ∣ a * b → 2 ∣ b) := by
  constructor
  · -- Proof of (i): If a divides 2n, then a divides n
    intro h
    rw [h₀] at h
    rcases h with ⟨k, hk⟩
    have h2 : (2 * n : ℤ) = (2 * t - 1) * k := by
      linarith
    have h3 : k % 2 = 0 := by
      have h4 : (2 * n : ℤ) % 2 = 0 := by
        omega
      have h5 : ((2 * t - 1) * k : ℤ) % 2 = 0 := by
        omega
      simp [Int.mul_emod, Int.add_emod, Int.sub_emod] at h5
      omega
    have h4 : ∃ m : ℤ, k = 2 * m := by
      have h5 : k % 2 = 0 := h3
      refine' ⟨k / 2, by omega⟩
    rcases h4 with ⟨m, hm⟩
    have h6 : (2 * n : ℤ) = 2 * ( (2 * t - 1) * m ) := by
      rw [show (2 * t - 1) * k = (2 * t - 1) * (2 * m) by rw [hm]; all_goals ring] at h2
      linarith
    have h7 : (n : ℤ) = (2 * t - 1) * m := by
      linarith
    rw [show a = 2 * t - 1 by linarith [h₀]]
    use m
    all_goals linarith
  · -- Proof of (ii): If 2 divides a * b, then 2 divides b
    intro h
    rw [h₀] at h
    have h1 : (2 : ℤ) ∣ (2 * t - 1) * b := h
    have h6 : (2 : ℤ) ∣ b := by
      have h2 : (2 * t - 1 : ℤ) % 2 = 1 := by
        omega
      have h5 : ( (2 * t - 1) * b ) % 2 = 0 := by
        omega
      have h7 : b % 2 = 0 := by
        simp [Int.mul_emod, h2] at h5
        omega
      exact Int.dvd_of_emod_eq_zero h7
    exact h6