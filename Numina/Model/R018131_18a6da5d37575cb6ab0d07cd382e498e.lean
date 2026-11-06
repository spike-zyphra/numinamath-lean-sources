import Mathlib

theorem algebra_16333 {f : ℕ → ℤ} (h1 : ∀ a b, f (a + b) = f a + f b - 2 * f (a * b)) (h2 : f 1 = 1) :
    f 1986 = 0 := by
  have h3 : ∀ (n : ℕ), f n = (n : ℤ) % 2 := by
    intro n 
    induction n with
    | zero =>
      have h0 : f 0 = 0 := by 
        specialize h1 0 0 
        simp at h1 
        linarith 
      simp [h0]
    | succ n ih =>
      have h4 : f (n + 1) = f n + f 1 - 2 * f (n * 1) := by
        specialize h1 n 1 
        simpa using h1 
      rw [h4]
      rw [ih]
      norm_num [h2]
      <;> omega
  specialize h3 1986 
  norm_num at h3 ⊢ 
  <;> omega