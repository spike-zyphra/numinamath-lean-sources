import Mathlib

theorem number_theory_188085 (n : ℤ) :
    ⌊(n / 2 : ℝ)⌋ + ⌊((n + 1) / 2 : ℝ)⌋ = n := by 
  by_cases h : n % 2 = 0 
  · -- Assume n is even 
    have h1 : ∃ k, n = 2 * k := by 
      refine' ⟨n / 2, by 
        omega⟩ 
    rcases h1 with ⟨k, h2⟩ 
    have h3 : ⌊(n / 2 : ℝ)⌋ = k := by 
      rw [h2]
      norm_num 
      <;> ring_nf <;> norm_num 
    have h4 : ⌊((n + 1) / 2 : ℝ)⌋ = k := by 
      rw [h2]
      norm_num 
      <;> ring_nf <;> norm_num 
    rw [h3, h4] 
    linarith 
  · -- Assume n is odd 
    have h1 : n % 2 = 1 := by 
      omega 
    have h2 : ∃ k, n = 2 * k + 1 := by 
      refine' ⟨(n - 1) / 2, by 
        omega⟩ 
    rcases h2 with ⟨k, h3⟩ 
    have h4 : ⌊(n / 2 : ℝ)⌋ = k := by 
      rw [h3]
      norm_num 
      <;> ring_nf <;> norm_num 
    have h5 : ⌊((n + 1) / 2 : ℝ)⌋ = k + 1 := by 
      rw [h3]
      norm_num 
      <;> ring_nf <;> norm_num 
    rw [h4, h5] 
    linarith