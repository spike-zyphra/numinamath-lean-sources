import Mathlib

theorem algebra_99792 {f : ℝ → ℝ} (h : ∀ a b, f (a + b) = f a * f b) (h' : f 1 = 1) :
    ∑ i ∈ Finset.range 2004, f (i + 2) / f (i + 1) = 2004 := by

  have h1 : ∀ n : ℕ, f ((↑n : ℝ) ) = 1 := by
    intro n
    induction n with
    | zero =>
      have h0 : f (0 : ℝ) = 1 := by
        have eq1 := h 1 0
        have eq2 : f (1 + (0 : ℝ)) = f 1 * f 0 := by simpa using eq1
        have eq3 : f (1 + (0 : ℝ)) = f 1 := by simp
        rw [eq3] at eq2
        rw [h'] at eq2
        linarith
      simpa using h0
    | succ n ih =>
      have eq5 : f ((↑(n + 1 : ℕ) : ℝ)) = f ((↑n : ℝ) ) * f 1 := by
        specialize h (↑n : ℝ) 1
        have eq6 : ((↑n : ℝ) + (1 : ℝ)) = (↑(n + 1 : ℕ) : ℝ) := by simp
        rw [eq6] at h
        simpa using h
      rw [eq5]
      rw [ih]
      rw [h']
      all_goals norm_num

  have eq5 : ∀ i : ℕ, f ((↑i + 2 : ℝ) ) / f ((↑i + 1 : ℝ) ) = 1 := by
    intro i
    have h21 : f ((↑i + 2 : ℝ) ) = f ((↑i + 1 : ℝ) ) * f 1 := by
      specialize h (↑i + 1) 1
      have eq4 : (↑i + 1 + (1 : ℝ)) = (↑i + 2) := by ring
      rw [eq4] at h
      simpa using h

    have h211 : f ((↑i + 2 : ℝ) ) = f ((↑i + 2 : ℝ) ) := by rfl
    have h2 : f ((↑i + 1 : ℝ) ) = 1 := by
      specialize h1 (i + 1)
      simpa using h1
    have h4 : f ((↑i + 2 : ℝ) ) = 1 := by
      have : f ((↑i + 2 : ℝ) ) = 1 := by
        specialize h1 (i + 2)
        simpa using h1
      linarith
    rw [h4, h2]
    all_goals norm_num [h']
    all_goals linarith
  rw [Finset.sum_congr rfl (fun i _ => eq5 i)]
  norm_num
  all_goals norm_num
  all_goals norm_num
  all_goals linarith