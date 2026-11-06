import Mathlib

theorem algebra_197481 {f : ℤ → ℤ} (h0 : f 0 = 1) (h : ∀ x, f (x + 3) = f x + 2 * x + 3) :
    f 1500 = 750001 := by

  -- Prove f(3n) = 1 + 3n^2 for all natural n 
  have h1 : ∀ (n : ℕ), f (3 * (n : ℤ)) = 1 + 3 * ((n : ℤ) )^2 := by 
    intro n 
    induction n with 
    | zero =>
      norm_num [h0]
    | succ n ih =>
      have eq1 : f (3 * ((n + 1 : ℕ) : ℤ) ) = f (3 * ((n : ℕ) : ℤ) + 3 ) := by 
        simp [mul_add, add_mul]
        <;> ring_nf 
      have eq2 : f (3 * ((n : ℕ) : ℤ) + 3 ) = f (3 * ((n : ℕ) : ℤ) ) + 2 * (3 * ((n : ℕ) : ℤ) ) + 3 := by
        specialize h (3 * ((n : ℕ) : ℤ) )
        simpa using h 
      rw [eq1, eq2] 
      rw [ih]
      simp [pow_two]
      <;> ring_nf 
  have h2 : f 1500 = 750001 := by
    specialize h1 500 
    norm_num at h1 ⊢ 
    linarith 
  linarith [h2]