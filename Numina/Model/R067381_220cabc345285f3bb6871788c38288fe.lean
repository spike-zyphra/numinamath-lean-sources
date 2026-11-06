import Mathlib

theorem algebra_292078 (a : ℕ → ℕ) (h₀ : ∀ n, a n = a (n - 1) * a 0 ^ 2)
    (h₁ : a 0 ≠ 0) :
    a 0 * a 2 * a 4 * a 6 = a 3 ^ 4 := by
  -- First, we need to establish expressions for a 1
  have eq_a1 : a 1 = a 0 ^ 3 := by
    specialize h₀ 1
    simp at h₀
    rw [h₀]
    all_goals ring_nf
    <;> tauto
  
  have eq_a2 : a 2 = a 0 ^ 5 := by 
    specialize h₀ 2
    simp at h₀
    rw [h₀]
    -- Now, a 2 = a 1 * a 0 ^ 2, we can rewrite a 1
    rw [eq_a1]
    all_goals ring_nf

  have eq_a3 : a 3 = a 0 ^ 7 := by
    specialize h₀ 3
    simp at h₀
    rw [h₀]
    -- Now, a 3 = a 2 * a 0 ^ 2, we can rewrite a 2
    rw [eq_a2]
    all_goals ring_nf

  have eq_a4 : a 4 = a 0 ^ 9 := by
    specialize h₀ 4
    simp at h₀
    rw [h₀]
    -- Now, a 4 = a 3 * a 0 ^ 2, we can rewrite a 3
    rw [eq_a3]
    all_goals ring_nf
  
  have eq_a5 : a 5 = a 0 ^ 11 := by
    specialize h₀ 5
    simp at h₀
    rw [h₀]
    -- Now, a 5 = a 4 * a 0 ^ 2, we can rewrite a 4
    rw [eq_a4]
    all_goals ring_nf
  
  have eq_a6 : a 6 = a 0 ^ 13 := by
    specialize h₀ 6
    simp at h₀
    rw [h₀]
    -- Now, a 6 = a 5 * a 0 ^ 2, we can rewrite a 5
    rw [eq_a5]
    all_goals ring_nf
  
  calc
    a 0 * a 2 * a 4 * a 6 = a 0 * (a 0 ^ 5) * (a 0 ^ 9) * (a 0 ^ 13) := by 
      rw [eq_a2, eq_a4, eq_a6]
    _ = a 0 ^ 28 := by 
      ring_nf
    _ = a 3 ^ 4 := by
      rw [eq_a3]
      all_goals ring_nf
      <;> tauto