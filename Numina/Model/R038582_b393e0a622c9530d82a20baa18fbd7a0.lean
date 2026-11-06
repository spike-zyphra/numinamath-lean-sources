import Mathlib

theorem algebra_312954 {f : ℝ → ℝ} (h : ∀ x, f (x + 3) = -1 / f x) (h0 : f 0 = 2) :
    f 2013 = -1 / 2 := by
  have h3 : f 3 = -1 / 2 := by
    specialize h 0
    rw [show (0 : ℝ ) + 3 = (3 : ℝ ) by norm_num] at h
    rw [h0] at h
    norm_num at h ⊢
    <;> linarith
  have h6 : f 6 = (2 : ℝ ) := by
    specialize h 3
    rw [show (3 : ℝ ) + 3 = (6 : ℝ ) by norm_num] at h
    rw [h3] at h
    norm_num at h ⊢
    <;> linarith

  have h1 : ∀ n : ℕ, f ((6 * (n : ℝ)) + 3) = -1 / 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
      <;> linarith [h3]
    | succ n ih =>
      have eq2 : (6 * ((n + 1 : ℕ) : ℝ)) + 3 = (6 * ((n : ℝ)) + 3) + 6 := by
        simp at *
        <;> ring_nf <;> norm_num
      rw [eq2]
      have eq1 : f ((6 * ((n : ℝ)) + 3) + 6) = f (6 * ((n : ℝ)) + 3) := by
        have h2 : f ((6 * ((n : ℝ)) + 3) + 3) = -1 / f (6 * ((n : ℝ)) + 3) := by
          specialize h (6 * ((n : ℝ)) + 3)
          simpa using h
        have h3' : f ((6 * ((n : ℝ)) + 3) + 6) = -1 / f ((6 * ((n : ℝ)) + 3) + 3) := by
          specialize h ((6 * ((n : ℝ)) + 3) + 3)
          ring_nf at h ⊢
          linarith
        rw [h3']
        rw [h2]
        field_simp at *
        <;> linarith [ih]
      rw [eq1]
      all_goals try linarith [ih]
  have eq2 : (2013 : ℝ ) = (6 * (335 : ℕ) + 3 : ℝ ) := by
    norm_num
  rw [eq2]
  specialize h1 335
  all_goals norm_num at h1 ⊢
  <;> linarith [h1]
  all_goals norm_num at h1 ⊢