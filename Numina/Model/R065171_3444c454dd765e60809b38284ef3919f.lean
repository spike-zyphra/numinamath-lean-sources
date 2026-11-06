import Mathlib

theorem algebra_305981 (f : ℕ → ℤ) (h : ∀ x y, f (x + y) = f x + f y + x * y) (h1 : f 1 = 1) :
    ∀ n, f n = n * (n + 1) / 2 := by 
  intro n
  induction n with
  | zero =>
    have h0 : f 0 = 0 := by
      have eq1 : f 0 = f 0 + f 0 + (0 : ℕ) * (0 : ℕ) := by
        specialize h 0 0
        simpa using h
      simp at eq1 
      linarith 
    simp [h0]
  | succ n ih =>
    have eq1 : f (n + 1) = f n + f 1 + n * (1 : ℕ) := by 
      specialize h n 1
      simpa using h
    rw [h1] at eq1 
    rw [ih] at eq1 
    simp [eq1]
    <;> ring_nf <;> omega