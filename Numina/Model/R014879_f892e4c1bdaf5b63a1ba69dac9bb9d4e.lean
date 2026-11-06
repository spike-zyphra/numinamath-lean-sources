import Mathlib

theorem algebra_314162 {f : ℝ → ℝ} (hodd : Odd f) (hf2 : f 2 = 0)
    (hf : ∀ x, f (x + 4) = f x + f 2) :
    f 1998 = 0 := by
  have h4 : ∀ x, f (x + 4) = f x := by
    intro x
    specialize hf x
    rw [hf2] at hf
    linarith
  have h1 : ∀ (n : ℕ), f ((2 : ℝ) + (n : ℝ) * (4 : ℝ)) = f 2 := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      have eq1 : ((2 : ℝ) + ((n + 1 : ℕ) : ℝ) * (4 : ℝ)) = ((2 : ℝ) + (n : ℝ) * (4 : ℝ)) + 4 := by
        simp at *
        <;> ring
      rw [eq1]
      rw [h4]
      all_goals
        try tauto
        <;> try linarith
  have eq3 : (1998 : ℝ) = (2 : ℝ) + (499 : ℝ) * (4 : ℝ) := by
    norm_num
  have h2 : f (1998 : ℝ) = f 2 := by
    rw [show (1998 : ℝ) = (2 : ℝ) + (499 : ℝ) * (4 : ℝ) by norm_num]
    specialize h1 499
    simpa using h1
  rw [h2, hf2]
  <;> try tauto