import Mathlib

theorem number_theory_188096 (n : ℤ) : ⌊(n / 2 : ℝ)⌋ * ⌊((n + 1) / 2 : ℝ)⌋ = ⌊(n ^ 2 / 4 : ℝ)⌋ := by 
  by_cases h : n % 2 = 0
  · -- Case n is even
    have h1 : ∃ k : ℤ, n = 2 * k := by
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    have h2 : ⌊(n / 2 : ℝ)⌋ = k := by
      rw [show (n : ℝ) = (2 * k : ℝ) by exact_mod_cast hk]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    have h3 : ⌊((n + 1) / 2 : ℝ)⌋ = k := by
      have : (n + 1 : ℝ) = (2 * k + 1 : ℝ) := by
        have h1' : (n : ℝ) = (2 * k : ℝ) := by exact_mod_cast hk
        linarith
      rw [this]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    have h4 : ⌊(n ^ 2 / 4 : ℝ)⌋ = k ^ 2 := by
      rw [show (n : ℝ) = (2 * k : ℝ) by exact_mod_cast hk]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    rw [h2, h3, h4]
    <;> ring
  · -- Case n is odd
    have h2 : n % 2 = 1 := by
      omega
    have h1 : ∃ k : ℤ, n = 2 * k + 1 := by
      have h3 : n % 2 = 1 := h2
      have h4 : n = 2 * (n / 2) + 1 := by 
        omega
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    have h2 : ⌊(n / 2 : ℝ)⌋ = k := by
      rw [show (n : ℝ) = (2 * k + 1 : ℝ) by exact_mod_cast hk]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    have h3 : ⌊((n + 1) / 2 : ℝ)⌋ = k + 1 := by
      have : (n + 1 : ℝ) = (2 * k + 2 : ℝ) := by
        have h1' : (n : ℝ) = (2 * k + 1 : ℝ) := by exact_mod_cast hk
        linarith
      rw [this]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    have h4 : ⌊(n ^ 2 / 4 : ℝ)⌋ = k ^ 2 + k := by
      rw [show (n : ℝ) = (2 * k + 1 : ℝ) by exact_mod_cast hk]
      simp [Int.floor_eq_iff]
      <;> ring_nf <;> norm_num
    rw [h2, h3, h4]
    <;> ring