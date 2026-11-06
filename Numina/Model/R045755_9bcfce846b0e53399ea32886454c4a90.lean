import Mathlib

theorem algebra_300436 {f : ℝ → ℝ} (h1 : f 1 = 2) (hf : ∀ x, f (x + 1) = (1 + f x) / (1 - f x)) :
    f 2016 = 1 / 3 := by

  have h2 : f 2 = -3 := by
    specialize hf 1
    rw [show (1 : ℝ) + 1 = (2 : ℝ) by norm_num] at hf
    rw [h1] at hf
    norm_num at hf ⊢
    all_goals linarith

  have h3 : f 3 = -1 / 2 := by
    specialize hf 2
    rw [show (2 : ℝ) + 1 = (3 : ℝ) by norm_num] at hf
    rw [h2] at hf
    norm_num at hf ⊢
    all_goals linarith

  have h4 : f 4 = 1 / 3 := by
    specialize hf 3
    rw [show (3 : ℝ) + 1 = (4 : ℝ) by norm_num] at hf
    rw [h3] at hf
    norm_num at hf ⊢
    all_goals linarith

  have h5 : f 5 = 2 := by
    specialize hf 4
    rw [show (4 : ℝ) + 1 = (5 : ℝ) by norm_num] at hf
    rw [h4] at hf
    norm_num at hf ⊢
    all_goals linarith

  have h6 : ∀ k : ℕ, f (4 * (k : ℝ)) = 1 / 3 := by 
    intro k 
    induction k with 
    | zero =>
      have eq1 : f 1 = (1 + f (0 : ℝ)) / (1 - f (0 : ℝ)) := by
        specialize hf (0 : ℝ)
        rw [show (0 : ℝ) + 1 = (1 : ℝ) by norm_num] at hf
        simpa using hf
      rw [h1] at eq1

      have h10 : f (0 : ℝ) ≠ 1 := by
        by_contra h
        rw [h] at eq1
        norm_num at eq1

      have eq4 : 2 * (1 - f (0 : ℝ)) = 1 + f (0 : ℝ) := by 
        have h2 : (1 - f (0 : ℝ)) ≠ 0 := by 
          intro h 
          apply h10 
          linarith 
        field_simp [h2] at eq1 ⊢ 
        linarith
      have eq5 : f (0 : ℝ) = 1 / 3 := by 
        linarith
      norm_num at *
      all_goals exact_mod_cast eq5
    | succ k ih =>
      have eq0 : f (4 * ((k : ℕ) : ℝ)) = 1 / 3 := ih
      have eq1 : f (4 * ((k + 1 : ℕ) : ℝ)) = f (4 * ((k : ℝ)) + 4) := by
        simp at *
        <;> ring_nf <;> norm_num
      rw [eq1] 
      have eq1' : f (4 * ((k : ℝ)) + 1) = 2 := by 
        have eq11 := hf (4 * ((k : ℝ)))
        rw [eq0] at eq11 
        rw [show 4 * ((k : ℝ)) + 1 = (4 * ((k : ℝ)) + 1 : ℝ) by ring] at *
        norm_num at eq11 ⊢ 
        all_goals linarith
      have eq2 : f (4 * ((k : ℝ)) + 2) = -3 := by
        have eq22 := hf (4 * ((k : ℝ)) + 1)
        rw [eq1'] at eq22
        rw [show 4 * ((k : ℝ)) + 2 = (4 * ((k : ℝ)) + 1 + 1 : ℝ) by ring] at *
        norm_num at eq22 ⊢ 
        all_goals linarith
      have eq3 : f (4 * ((k : ℝ)) + 3) = -1 / 2 := by 
        have eq33 := hf (4 * ((k : ℝ)) + 2)
        rw [eq2] at eq33 
        rw [show 4 * ((k : ℝ)) + 3 = (4 * ((k : ℝ)) + 2 + 1 : ℝ) by ring] at *
        norm_num at eq33 ⊢ 
        all_goals linarith
      have eq4 : f (4 * ((k : ℝ)) + 4) = 1 / 3 := by
        have eq44 := hf (4 * ((k : ℝ)) + 3)
        rw [eq3] at eq44 
        rw [show 4 * ((k : ℝ)) + 4 = (4 * ((k : ℝ)) + 3 + 1 : ℝ) by ring] at *
        norm_num at eq44 ⊢ 
        all_goals linarith
      exact_mod_cast eq4 
  have h7 : (2016 : ℝ) = 4 * (504 : ℝ) := by norm_num 
  rw [h7]
  specialize h6 504 
  norm_num at h6 ⊢ 
  all_goals linarith