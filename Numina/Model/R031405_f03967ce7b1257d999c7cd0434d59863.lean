import Mathlib

theorem number_theory_4976
    (n : ℤ)
    (h : Odd n) :
    ∃ k, n^2 = 8 * k + 1 := by
  have h1 : n % 8 = 1 ∨ n % 8 = 3 ∨ n % 8 = 5 ∨ n % 8 = 7 := by
    have h2 : n % 2 = 1 := by 
      obtain ⟨m, hm⟩ := h
      omega
    omega
  rcases h1 with (h1 | h1 | h1 | h1)
  · -- Case n % 8 = 1
    have h2 : n ^ 2 % 8 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h3 : ∃ k, n ^ 2 = 8 * k + 1 := by 
      have h4 : n ^ 2 % 8 = 1 := h2
      refine' ⟨(n ^ 2 - 1) / 8, by 
        omega⟩
    exact h3
  · -- Case n % 8 = 3
    have h2 : n ^ 2 % 8 = 1 := by
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h3 : ∃ k, n ^ 2 = 8 * k + 1 := by 
      have h4 : n ^ 2 % 8 = 1 := h2 
      refine' ⟨(n ^ 2 - 1) / 8, by 
        omega⟩
    exact h3
  · -- Case n % 8 = 5
    have h2 : n ^ 2 % 8 = 1 := by 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h3 : ∃ k, n ^ 2 = 8 * k + 1 := by 
      have h4 : n ^ 2 % 8 = 1 := h2
      refine' ⟨(n ^ 2 - 1) / 8, by 
        omega⟩
    exact h3
  · -- Case n % 8 = 7
    have h2 : n ^ 2 % 8 = 1 := by 
      simp [pow_two, Int.add_emod, Int.mul_emod, h1]
    have h3 : ∃ k, n ^ 2 = 8 * k + 1 := by 
      have h4 : n ^ 2 % 8 = 1 := h2
      refine' ⟨(n ^ 2 - 1) / 8, by 
        omega⟩
    exact h3