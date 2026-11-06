import Mathlib
theorem number_theory_611075 (n : ℤ) : ⌊(↑n : ℝ) / 2⌋ + ⌊((↑n : ℝ) + 1) / 2⌋ = n:= by
  by_cases h : n % 2 = 0
  · -- Assume n is even
    have h1 : ∃ k : ℤ, n = 2 * k := by 
      refine' ⟨n / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    have h2 : (↑n : ℝ) = (↑(2 * k) : ℝ) := by
      rw [hk]
    rw [h2]
    norm_num [Int.floor_eq_iff, mul_add, add_mul]
    <;> ring_nf <;> norm_num
    <;> omega
  · -- Assume n is odd
    have h2 : n % 2 = 1 := by 
      omega
    have h1 : ∃ k : ℤ, n = 2 * k + 1 := by 
      refine' ⟨(n - 1) / 2, by omega⟩
    rcases h1 with ⟨k, hk⟩
    have h3 : (↑n : ℝ) = (↑(2 * k + 1) : ℝ) := by
      rw [hk]
    rw [h3]
    norm_num [Int.floor_eq_iff, mul_add, add_mul]
    <;> ring_nf <;> norm_num
    <;> omega