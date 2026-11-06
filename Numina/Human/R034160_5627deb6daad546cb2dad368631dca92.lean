import Mathlib

theorem number_theory_256711 :
    {(m, n) | 2^n + 1 = m^2} = {(3, 3)} := by
  ext ⟨m, n⟩
  simp
  constructor
  swap
  {
    rintro ⟨rfl, rfl⟩
    simp
  }
  intro h
  have h₀ : 1 ≤ m := by
    by_contra! hm
    simp at hm
    simp [hm] at h
  have h₁ : 2^n = (m + 1) * (m - 1) := by
    zify at h ⊢
    simp [h₀]
    linear_combination h
  obtain ⟨s, -, hs⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show (m + 1) ∣ 2^n from ⟨m - 1, h₁⟩)
  obtain ⟨t, -, ht⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show (m - 1) ∣ 2^n from ⟨m + 1, by linear_combination h₁⟩)
  have h₂ : 2 ^ s = 2 ^ t + 2 := by omega
  have h₃ : t < s := (Nat.pow_lt_pow_iff_right (show 1 < 2 by simp)).mp (by omega)
  apply Nat.pow_le_pow_of_le (show 1 < 2 by simp) at h₃
  simp [pow_succ] at h₃
  have h₄ : 2 ^ t ≤ 2 ^ 1 := by omega
  rw [Nat.pow_le_pow_iff_right (by simp)] at h₄
  interval_cases t
  . obtain rfl : m = 2 := by omega
    simp at hs
    have h₅ : s ≠ 0 := by
      rintro rfl
      simp at hs
    have h₆ := dvd_pow_self 2 h₅
    rw [← hs] at h₆
    norm_num at h₆
  . obtain rfl : m = 3 := by omega
    have h₅ : 2 ^ n = 2 ^ 3 := by omega
    rw [pow_right_inj₀ (by simp) (by simp)] at h₅
    simp [h₅]
