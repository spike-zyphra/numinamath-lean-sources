import Mathlib

theorem number_theory_3238 (N : ℕ) :
    (∀ c ∈ Finset.Icc 1 9, c ≠ 0 → (10 * N + c) % c = 0) ↔ N ≡ 0 [MOD 252] := by
  constructor
  · -- Forward direction: if ∀ c ∈ {1, ..., 9}, c ≠ 0 → (10N + c) % c = 0, then N ≡ 0 [MOD 252]
    intro h
    have h3 : N % 3 = 0 := by
      have h3' : (10 * N + 3) % 3 = 0 := by
        apply h 3
        · -- Show 3 ∈ Finset.Icc 1 9
          simp
        all_goals
          norm_num
      omega
    have h4 : N % 4 = 0 := by
      have h8' : (10 * N + 8) % 8 = 0 := by
        apply h 8
        · -- Show 8 ∈ Finset.Icc 1 9
          simp
        all_goals
          norm_num
      omega
    have h7 : N % 7 = 0 := by
      have h7' : (10 * N + 7) % 7 = 0 := by
        apply h 7
        · -- Show 7 ∈ Finset.Icc 1 9
          simp
        all_goals
          norm_num
      omega
    have h9 : N % 9 = 0 := by
      have h9' : (10 * N + 9) % 9 = 0 := by
        apply h 9
        · -- Show 9 ∈ Finset.Icc 1 9
          simp
        all_goals
          norm_num
      omega
    have h252 : N % 252 = 0 := by
      omega
    show N ≡ 0 [MOD 252]
    simp [Nat.ModEq] at *
    omega
  · -- Backward direction: if N ≡ 0 [MOD 252], then ∀ c ∈ {1, ..., 9}, c ≠ 0 → (10N + c) % c = 0
    intro h c hc hcne
    have hN : N % 252 = 0 := h
    have h1 : c ≥ 1 := by
      have h2 : c ∈ Finset.Icc 1 9 := hc
      simp at h2 ⊢
      omega
    have h2 : c ≤ 9 := by
      have h2 : c ∈ Finset.Icc 1 9 := hc
      simp at h2 ⊢
      omega
    interval_cases c <;> simp_all [Nat.ModEq] <;> omega