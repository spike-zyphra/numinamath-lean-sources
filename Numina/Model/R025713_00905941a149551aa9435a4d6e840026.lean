import Mathlib

theorem algebra_197724 {f : ℤ → ℤ} (hf0 : f 0 = 1) (hfx : ∀ x, f (x + 3) = f x + 2 * x + 3) :
    f 6000 = 12000001 := by
  have h1 : ∀ (n : ℕ), f (3 * (n : ℤ)) = 1 + 3 * ((n : ℤ) ) ^ 2 := by
    intro n 
    induction n with
    | zero =>
      norm_num [hf0]
    | succ n ih =>
      have eq1 : f (3 * ((n + 1 : ℕ) : ℤ) ) = f (3 * ((n : ℕ) : ℤ) + 3 ) := by
        simp at *
        <;> ring_nf
      rw [eq1]
      rw [show 3 * ((n : ℕ) : ℤ) + 3 = (3 * ((n : ℕ) : ℤ) ) + 3 by ring]
      rw [hfx]
      rw [ih]
      simp [pow_two]
      <;> ring_nf
  have h2 : f 6000 = 1 + 3 * ((2000 : ℤ) ) ^ 2 := by
    specialize h1 2000
    norm_num at h1 ⊢
    linarith
  rw [h2]
  norm_num