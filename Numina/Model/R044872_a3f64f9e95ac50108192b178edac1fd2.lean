import Mathlib

theorem algebra_227922 {f : ℤ → ℤ} (h : ∀ x, f (x + 1) = f x + 2 * x + 3) (h0 : f 0 = 1) :
    f 2012 = 2013 ^ 2 := by
  have h2 : ∀ (x : ℕ), f x = (x + 1) ^ 2 := by 
    intro x 
    induction x with
    | zero =>
      norm_num [h0]
    | succ m ih =>
      have eq1 : f (↑(m + 1) ) = f (↑m) + 2 * (↑m : ℤ) + 3 := by 
        specialize h (↑m : ℤ)
        simpa using h 
      rw [eq1] at *
      rw [ih]
      simp [add_sq, mul_add, add_mul]
      <;> ring_nf <;> omega 
  have eq3 : f 2012 = (2012 + 1) ^ 2 := by 
    exact_mod_cast h2 2012
  norm_num at eq3 ⊢
  all_goals linarith