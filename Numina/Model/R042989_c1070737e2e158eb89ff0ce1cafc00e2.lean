import Mathlib

open Real

theorem algebra_312195 {f : ℝ → ℝ}
    (h₀ : ∀ x, x ≤ 0 → f x = logb 2 (1 - x))
    (h₁ : ∀ x, x > 0 → f x = f (x - 1) - f (x - 2)) :
    f 2014 = 1 := by

  have h2 : f 0 = 0 := by
    specialize h₀ 0 (by norm_num)
    rw [h₀]
    norm_num [logb_eq_iff_rpow_eq]

  have h3 : f (-1 : ℝ) = 1 := by
    specialize h₀ (-1 : ℝ) (by norm_num)
    rw [h₀]
    norm_num [logb_eq_iff_rpow_eq]

  have h4 : f 1 = -1 := by
    specialize h₁ 1 (by norm_num)
    rw [show (1 : ℝ) - 1 = (0 : ℝ) by norm_num, show (1 : ℝ) - 2 = (-1 : ℝ) by norm_num] at h₁
    rw [h₁, h2, h3]
    all_goals norm_num

  have h5 : f 2 = -1 := by
    specialize h₁ 2 (by norm_num)
    rw [show (2 : ℝ) - 1 = (1 : ℝ) by norm_num, show (2 : ℝ) - 2 = (0 : ℝ) by norm_num] at h₁
    rw [h₁, h4, h2]
    all_goals norm_num

  have h6 : f 3 = 0 := by
    specialize h₁ 3 (by norm_num)
    rw [show (3 : ℝ) - 1 = (2 : ℝ) by norm_num, show (3 : ℝ) - 2 = (1 : ℝ) by norm_num] at h₁
    rw [h₁, h5, h4]
    all_goals norm_num

  have h7 : f 4 = 1 := by
    specialize h₁ 4 (by norm_num)
    rw [show (4 : ℝ) - 1 = (3 : ℝ) by norm_num, show (4 : ℝ) - 2 = (2 : ℝ) by norm_num] at h₁
    rw [h₁, h6, h5]
    all_goals norm_num

  have eq4 : ∀ (k : ℕ), f (4 + ↑k * 6 : ℝ) = 1 := by
    intro k
    induction k with
    | zero =>
      norm_num
      all_goals
      linarith [h7]
    | succ m ih =>
      have eq5 : (4 + ↑(m + 1 : ℕ) * 6 : ℝ) = (4 + ↑m * 6 : ℝ) + 6 := by
        simp at *
        <;> ring
      rw [eq5]
      have h14 : ∀ x > 0, f (x + 6 : ℝ) = f x := by
        intro x hx
        have eq5 : f (x + 6 : ℝ) = f (x + 5 : ℝ) - f (x + 4 : ℝ) := by
          specialize h₁ (x + 6 : ℝ) (by linarith)
          rw [show (x + 6 : ℝ) - 1 = x + 5 by ring, show (x + 6 : ℝ) - 2 = x + 4 by ring] at h₁
          linarith
        have eq6 : f (x + 5 : ℝ) = f (x + 4 : ℝ) - f (x + 3 : ℝ) := by
          specialize h₁ (x + 5 : ℝ) (by linarith)
          rw [show (x + 5 : ℝ) - 1 = x + 4 by ring, show (x + 5 : ℝ) - 2 = x + 3 by ring] at h₁
          linarith
        have eq7 : f (x + 4 : ℝ) = f (x + 3 : ℝ) - f (x + 2 : ℝ) := by
          specialize h₁ (x + 4 : ℝ) (by linarith)
          rw [show (x + 4 : ℝ) - 1 = x + 3 by ring, show (x + 4 : ℝ) - 2 = x + 2 by ring] at h₁
          linarith
        have eq8 : f (x + 3 : ℝ) = f (x + 2 : ℝ) - f (x + 1 : ℝ) := by
          specialize h₁ (x + 3 : ℝ) (by linarith)
          rw [show (x + 3 : ℝ) - 1 = x + 2 by ring, show (x + 3 : ℝ) - 2 = x + 1 by ring] at h₁
          linarith
        have eq9 : f (x + 2 : ℝ) = f (x + 1 : ℝ) - f (x : ℝ) := by
          specialize h₁ (x + 2 : ℝ) (by linarith)
          rw [show (x + 2 : ℝ) - 1 = x + 1 by ring, show (x + 2 : ℝ) - 2 = x by ring] at h₁
          linarith
        have eq10 : f (x + 1 : ℝ) = f (x : ℝ) - f (x - 1 : ℝ) := by
          specialize h₁ (x + 1 : ℝ) (by linarith)
          rw [show (x + 1 : ℝ) - 1 = x by ring, show (x + 1 : ℝ) - 2 = x - 1 by ring] at h₁
          linarith
        have eq12 : f (x + 6 : ℝ) = f x := by
          nlinarith [eq5, eq6, eq7, eq8, eq9, eq10]
        exact_mod_cast eq12
      have eq13 : f ((4 + ↑m * 6 : ℝ) + 6 : ℝ) = f (4 + ↑m * 6 : ℝ) := by
        specialize h14 (4 + ↑m * 6 : ℝ) (by
          positivity
        )
        simpa using h14
      rw [eq13, ih]
      all_goals norm_num
  -- Compute 2014 as 4 + 335*6
  have h12 : (2014 : ℝ) = (4 + ↑(335 : ℕ) * 6 : ℝ) := by
    norm_num
  rw [h12]
  specialize eq4 335
  norm_num at eq4 ⊢
  all_goals
    linarith [eq4]