import Mathlib

theorem algebra_197229 {f : ℤ → ℤ} (h₀ : f 0 = 1) (h₁ : ∀ x, f (x + 2) = f x + 4 * x + 2) :
    f 2000 = 3998001 := by

  have h2 : ∀ (n : ℕ), f (2 * (n : ℤ)) = 4 * ((n : ℤ) ) ^ 2 - 2 * ((n : ℤ) ) + 1 := by
    intro n 
    induction n with 
    | zero =>
      simp [h₀]
    | succ n ih =>
      have eq1 : f (2 * ((n + 1 : ℕ) : ℤ) ) = f (2 * ((n : ℕ) : ℤ) + 2) := by
        simp [mul_add, add_mul]
        <;> ring_nf
      have eq2 : f (2 * ((n : ℕ) : ℤ) + 2) = f (2 * ((n : ℕ) : ℤ) ) + 4 * (2 * ((n : ℕ) : ℤ) ) + 2 := by
        specialize h₁ (2 * ((n : ℕ) : ℤ) )
        simpa using h₁ 
      rw [eq1, eq2]
      rw [ih]
      simp [pow_two, mul_add, mul_assoc]
      <;> ring
  have h3 : f 2000 = 4 * ((1000 : ℤ) ) ^ 2 - 2 * ((1000 : ℤ) ) + 1 := by
    specialize h2 1000 
    norm_num at h2 ⊢ 
    try omega 
  rw [h3]
  norm_num