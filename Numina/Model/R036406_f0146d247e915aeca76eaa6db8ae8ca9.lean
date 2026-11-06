import Mathlib

theorem number_theory_60628 {a b : ℤ} (ha : 6 ∣ a) : ∃ (x1 x2 x3 x4 y1 y2 y3 y4 y5 : ℤ), a = x1^3 + x2^3 + x3^3 + x4^3 ∧ b = y1^3 + y2^3 + y3^3 + y4^3 + y5^3 := by
  have ha1 : ∃ k, a = 6 * k := by 
    refine' ⟨a / 6, by omega⟩
  rcases ha1 with ⟨k, hk⟩
  have h10 : 6 ∣ (b - b ^ 3 : ℤ) := by
    have h4 : (b - b ^ 3 : ℤ) % 2 = 0 := by
      have h5 : b % 2 = 0 ∨ b % 2 = 1 := by omega
      rcases h5 with (h5 | h5)
      · 
        simp [h5, Int.sub_emod, pow_succ, Int.mul_emod, h5]
      · 
        simp [h5, Int.sub_emod, pow_succ, Int.mul_emod, h5]
    have h6 : (b - b ^ 3 : ℤ) % 3 = 0 := by
      have h7 : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
      rcases h7 with (h7 | h7 | h7)
      · 
        simp [h7, Int.sub_emod, pow_succ, Int.mul_emod, h7]
      · 
        simp [h7, Int.sub_emod, pow_succ, Int.mul_emod, h7]
      · 
        simp [h7, Int.sub_emod, pow_succ, Int.mul_emod, h7]
    have h8 : (b - b ^ 3 : ℤ) % 6 = 0 := by
      omega
    exact Int.dvd_of_emod_eq_zero h8
  rcases h10 with ⟨m, hm⟩
  use k + 1, k - 1, -k, -k, b, m + 1, m - 1, -m, -m
  constructor
  · -- Show a = x1^3 + x2^3 + x3^3 + x4^3
    rw [hk]
    ring_nf
  · -- Show b = y1^3 + y2^3 + y3^3 + y4^3 + y5^3
    have hb2 : b = b^3 + (m+1)^3 + (m-1)^3 - m^3 - m^3 := by
      have h11 : b = b^3 + 6*m := by
        nlinarith
      have h12 : 6*m = (m+1)^3 + (m-1)^3 - m^3 - m^3 := by
        ring_nf
      linarith [h11, h12]
    nlinarith [hb2]