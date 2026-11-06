import Mathlib

theorem number_theory_135 (n : ℤ) (hn : n ≥ 24) :
    ∃ a b : ℕ, n = 5 * a + 7 * b := by
  have h1 : n ≥ 24 := hn
  have h2 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by
    omega
  rcases h2 with (h | h | h | h | h)
  · -- Case where n % 5 = 0
    use (n / 5).toNat, 0
    have h_eq : n = 5 * ((n / 5).toNat : ℤ) + 7 * (0 : ℤ) := by
      omega
    norm_num at h_eq ⊢
    omega
  · -- Case where n % 5 = 1
    use ((n - 21) / 5).toNat, 3
    have h_eq : n = 5 * ((n - 21) / 5).toNat + 7 * 3 := by
      omega
    norm_num at h_eq ⊢
    omega
  · -- Case where n % 5 = 2
    use ((n - 7) / 5).toNat, 1
    have h_eq : n = 5 * ((n - 7) / 5).toNat + 7 * 1 := by
      omega
    norm_num at h_eq ⊢
    omega
  · -- Case where n % 5 = 3
    use ((n - 28) / 5).toNat, 4
    have h_eq : n = 5 * ((n - 28) / 5).toNat + 7 * 4 := by
      omega
    norm_num at h_eq ⊢
    omega
  · -- Case where n % 5 = 4
    use ((n - 14) / 5).toNat, 2
    have h_eq : n = 5 * ((n - 14) / 5).toNat + 7 * 2 := by
      omega
    norm_num at h_eq ⊢
    omega