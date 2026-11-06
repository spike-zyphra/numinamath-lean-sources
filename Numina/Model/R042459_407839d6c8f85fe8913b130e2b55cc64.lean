import Mathlib

theorem algebra_10684 (n : ℤ) :
    ⌊(n ^ 2 / 4 : ℝ)⌋ - ⌊(n / 2 : ℝ)⌋ ^ 2 = 2 ↔ n = 5 := by
  constructor
  · -- Assume the equation holds: $\left\lfloor n^2/4 \right\rfloor - \lfloor n/2 \rfloor^2 = 2$, prove $n = 5$
    intro h_eq
    by_cases h : n % 2 = 0
    · -- Assume n is even
      have h2 : ∃ k : ℤ, n = 2 * k := by
        refine' ⟨n / 2, by omega⟩
      rcases h2 with ⟨k, rfl⟩
      have h3 : ⌊((2 * k : ℤ) ^ 2 / 4 : ℝ)⌋ = k ^ 2 := by
        norm_num [Int.floor_eq_iff]
        <;> ring_nf
        <;> norm_num
        <;> ring_nf
        <;> norm_num
      have h4 : ⌊((2 * k : ℤ) / 2 : ℝ)⌋ = k := by
        norm_num [Int.floor_eq_iff]
        <;> ring_nf 
        <;> norm_num 
        <;> ring_nf 
        <;> norm_num
      rw [h3, h4] at h_eq
      have h5 : k ^ 2 - k ^ 2 = 0 := by
        ring_nf
      have h6 : 0 = 2 := by 
        nlinarith
      omega
    · -- Assume n is odd
      have h2 : n % 2 = 1 := by 
        omega
      have h3 : ∃ k : ℤ, n = 2 * k + 1 := by
        refine' ⟨(n - 1) / 2, by omega⟩
      rcases h3 with ⟨k, rfl⟩
      have h4 : ⌊((2 * k + 1 : ℤ) ^ 2 / 4 : ℝ)⌋ = k^2 + k := by
        norm_num [Int.floor_eq_iff]
        <;> ring_nf 
        <;> norm_num 
        <;> ring_nf 
        <;> norm_num
      have h5 : ⌊((2 * k + 1 : ℤ) / 2 : ℝ)⌋ = k := by
        norm_num [Int.floor_eq_iff]
        <;> ring_nf 
        <;> norm_num
        <;> ring_nf 
        <;> norm_num
      rw [h4, h5] at h_eq
      have h6 : k = 2 := by
        nlinarith 
      have h7 : (2 * k + 1 : ℤ) = 5 := by
        linarith [h6]
      linarith [h7]
  · -- Assume n = 5, prove the equation holds
    intro h_eq
    rw [h_eq]
    norm_num [Int.floor_eq_iff]
    <;> norm_num
    <;> norm_num
    <;> norm_num
    <;> norm_num