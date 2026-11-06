import Mathlib

theorem algebra_197395 {f : ℤ → ℤ} (hf0 : f 0 = 1) (hfn : ∀ x, f (x + 2) = f x + 3 * x + 2) :
    f 4000 = 11998001 := by
  have h1 : ∀ (n : ℕ), f (2 * (n : ℤ)) = 1 + 3 * (n : ℤ) ^ 2 - (n : ℤ) := by 
    intro n 
    induction n with 
    | zero =>
      norm_num 
      <;> linarith [hf0]
    | succ n ih =>
      have eq1 : f (2 * ((n + 1 : ℕ) : ℤ)) = f (2 * ((n : ℕ) : ℤ) + 2) := by 
        simp [mul_add]
        <;> ring_nf 
      have eq2 : f (2 * ((n : ℕ) : ℤ) + 2) = f (2 * ((n : ℕ) : ℤ)) + 3 * (2 * ((n : ℕ) : ℤ)) + 2 := by 
        specialize hfn (2 * ((n : ℕ) : ℤ))
        simpa using hfn 
      rw [eq1]
      rw [eq2]
      rw [ih]
      simp [mul_add, add_mul]
      <;> ring_nf 
  have h2000 : f (4000 : ℤ) = 1 + 3 * (2000 : ℤ) ^ 2 - (2000 : ℤ) := by 
    specialize h1 2000 
    norm_num at h1 ⊢ 
    <;> try linarith 
  rw [h2000]
  norm_num