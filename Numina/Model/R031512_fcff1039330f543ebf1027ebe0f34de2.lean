import Mathlib

theorem number_theory_53411 : Set.Infinite {(x, y, z) : ℤ × ℤ × ℤ | x * y * z ≠ 0 ∧ x ^ 2 + y ^ 5 = z ^ 3} := by
  apply Set.infinite_of_injective_forall_mem (f := λ (n : ℕ) => (2 ^ (15 * n + 10), 2 ^ (6 * n + 4), 2 ^ (10 * n + 7)))
  · -- Show f is injective
    intro n m h
    simp [Prod.ext_iff] at h
    omega
  · -- Show that all elements of the image of f are in the set
    intro n 
    simp only [Set.mem_setOf_eq]
    have h₁ : ((2 : ℤ) ^ (15 * n + 10) : ℤ) * ((2 : ℤ) ^ (6 * n + 4) : ℤ) * ((2 : ℤ) ^ (10 * n + 7) : ℤ) ≠ 0 := by
      have h₁₁ : ((2 : ℤ) ^ (15 * n + 10) : ℤ) ≠ 0 := by
        positivity
      have h₁₂ : ((2 : ℤ) ^ (6 * n + 4) : ℤ) ≠ 0 := by
        positivity
      have h₁₃ : ((2 : ℤ) ^ (10 * n + 7) : ℤ) ≠ 0 := by
        positivity
      exact mul_ne_zero (mul_ne_zero h₁₁ h₁₂) h₁₃
    have h₂ : ((2 : ℤ) ^ (15 * n + 10) : ℤ) ^ 2 + ((2 : ℤ) ^ (6 * n + 4) : ℤ) ^ 5 = ((2 : ℤ) ^ (10 * n + 7) : ℤ) ^ 3 := by
      ring_nf
    exact ⟨h₁, h₂⟩