import Mathlib

theorem algebra_197163 {f : ℤ → ℤ} (h1 : f 1 = 1)
    (h2 : ∀ m n, f (m + n) = f m + f n + m * n) :
    f 2003 / 6 = 334501 := by

  have h3 : ∀ (n : ℕ), f (n : ℤ) = (n : ℤ) * ( (n : ℤ) + 1 ) / 2 := by
    intro n 
    induction n with
    | zero =>
      have h0 : f (0 : ℤ) = 0 := by 
        have eq1 := h2 0 0
        simp at eq1 
        linarith 
      simp [h0]
    | succ n ih =>
      have eq1 : f ( (↑n : ℤ) + 1 ) = f (↑n : ℤ ) + f (1 : ℤ ) + (↑n : ℤ ) * (1 : ℤ ) := by
        specialize h2 (↑n : ℤ ) (1 : ℤ )
        simpa using h2 
      have eq2 : (↑(n + 1 : ℕ) : ℤ ) = (↑n : ℤ ) + 1 := by
        simp [Nat.cast_add, Nat.cast_one] 
      have eq3 : f (↑(n + 1: ℕ) : ℤ ) = f ( (↑n : ℤ ) + 1 ) := by 
        rw [eq2] 
      have eq4 : f (↑(n + 1: ℕ) : ℤ ) = f (↑n : ℤ ) + f (1 : ℤ ) + (↑n : ℤ ) * (1 : ℤ ) := by 
        rw [eq3] 
        exact_mod_cast eq1 
      rw [eq4]
      rw [ih]
      rw [h1]
      all_goals simp [mul_add, add_mul, add_assoc]
      all_goals ring_nf <;> omega

  have h4 : f (2003 : ℤ) = 2003 * (1002 : ℤ ) := by 
    have h5 := h3 2003 
    norm_num at h5 ⊢ 
    linarith

  rw [h4] 
  all_goals norm_num