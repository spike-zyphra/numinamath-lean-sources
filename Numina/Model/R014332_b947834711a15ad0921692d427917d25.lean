import Mathlib

theorem algebra_2594 {f : ℝ → ℝ} (hf : ∀ x, f (x + 1) = f x + 4) (hf0 : f 0 = 3) :
    f (f (f 5)) = 383 := by
  have eq1 : ∀ (n : ℕ), f ((↑n : ℝ)) = 3 + 4 * (n : ℝ) := by
    intro n
    induction n with
    | zero =>
      simp [hf0]
    | succ n ih =>
      have h1 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑(n : ℕ) : ℝ) + 1) := by
        simp at *
        <;> ring_nf <;> norm_cast <;> simp
      rw [h1]
      rw [hf]
      rw [ih]
      simp [mul_add, add_mul]
      <;> ring_nf <;> norm_num
  -- Compute f(5)
  have h1 : f 5 = 23 := by
    specialize eq1 5
    norm_num at eq1 ⊢
    linarith
  -- Compute f(23)
  have h2 : f 23 = 95 := by
    have eq3 : ∀ (n : ℕ), f ((↑(n : ℕ) : ℝ) ) = f (0 : ℝ) + 4 * (↑(n : ℕ) : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h21 : f ((↑(n + 1 : ℕ) : ℝ) ) = f ((↑(n : ℕ) : ℝ) + 1) := by
          simp at *
          <;> ring_nf <;> norm_cast <;> simp
        rw [h21]
        rw [hf]
        rw [ih]
        simp [mul_add, add_mul]
        <;> ring_nf <;> norm_num
    specialize eq3 23
    norm_num [hf0] at eq3 ⊢
    linarith
  -- Compute f(95)
  have h3 : f 95 = 383 := by
    have eq3 : ∀ (n : ℕ), f ((↑(n : ℕ) : ℝ) ) = f (0 : ℝ) + 4 * (↑(n : ℕ) : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        have h21 : f ((↑(n + 1 : ℕ) : ℝ) ) = f ((↑(n : ℕ) : ℝ) + 1) := by
          simp at *
          <;> ring_nf <;> norm_cast <;> simp
        rw [h21]
        rw [hf]
        rw [ih]
        simp [mul_add, add_mul]
        <;> ring_nf <;> norm_num
    specialize eq3 95
    norm_num [hf0] at eq3 ⊢
    linarith
  rw [h1]
  rw [h2]
  rw [h3]
  all_goals norm_num