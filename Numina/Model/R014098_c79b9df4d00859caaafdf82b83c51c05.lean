import Mathlib

theorem number_theory_3120 (x y : Set ℤ)
    (hx : x = {p : ℤ | ∃ n : ℕ, p = 8 ^ n - 7 * n - 1})
    (hy : y = {p : ℤ | ∃ n : ℕ, p = 49 * (n - 1)}) :
    x ⊆ y := by
  rw [hx, hy]
  intro p hp 
  rcases hp with ⟨n, hp⟩
  have h5 : ∃ m : ℕ, (8 : ℤ) ^ n - 7 * (n : ℤ) - 1 = 49 * (m - 1) := by
    have h2 : ∀ n : ℕ, (8 : ℤ) ^ n % 49 = (1 + 7 * (n : ℤ)) % 49 := by
      intro n 
      induction n with 
      | zero =>
        norm_num
      | succ n ih =>
        simp [pow_succ, Int.add_emod, Int.mul_emod] at ih ⊢
        omega 
    have h3 : ∀ n : ℕ, 49 ∣ ((8 : ℤ) ^ n - 7 * (n : ℤ) - 1) := by
      intro n
      have h4 : (8 : ℤ) ^ n % 49 = (1 + 7 * (n : ℤ)) % 49 := h2 n
      have h5 : ((8 : ℤ) ^ n - 7 * (n : ℤ) - 1) % 49 = 0 := by 
        simp [Int.sub_emod, Int.add_emod, Int.mul_emod, h4] 
        all_goals omega 
      omega 
    have h4 : (8 : ℤ) ^ n - 7 * (n : ℤ) - 1 = 49 * ( ((8 : ℤ) ^ n - 7 * (n : ℤ) - 1) / 49 : ℤ) := by
      have h3' := h3 n 
      have h5 : ((8 : ℤ) ^ n - 7 * (n : ℤ) - 1) % 49 = 0 := by
        have h4 : (8 : ℤ) ^ n % 49 = (1 + 7 * (n : ℤ)) % 49 := h2 n
        simp [Int.sub_emod, Int.add_emod, Int.mul_emod, h4] 
        all_goals omega 
      omega 
    use (( (8 : ℤ) ^ n - 7 * (n : ℤ) - 1) / 49 + 1).toNat 
    have h7 : (( (8 : ℤ) ^ n - 7 * (n : ℤ) - 1) / 49 + 1).toNat = (( (8 : ℤ) ^ n - 7 * (n : ℤ) - 1 : ℤ) / 49 + 1 : ℤ) := by 
      simp [Int.toNat_of_nonneg] 
      all_goals 
      have h6 : ((8: ℤ) ^ n - 7 * (n : ℤ) - 1) / 49 ≥ 0 := by 
        have h3_0 : (8 : ℤ) ^ n ≥ 7 * (n : ℤ) + 1 := by 
          have h7 : ∀ (n : ℕ), (8 : ℤ) ^ n ≥ 7 * (n : ℤ) + 1 := by 
            intro n 
            induction n with
            | zero =>
              norm_num 
            | succ n ih =>
              simp [pow_succ] at ih ⊢ 
              all_goals omega 
          apply h7 n 
        omega 
      omega
    rw [h7] 
    omega 
  rcases h5 with ⟨m, hm⟩ 
  refine ⟨m, by 
    rw [hp] 
    linarith [hm]
  ⟩