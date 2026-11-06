import Mathlib

theorem algebra_299256 {f : ℝ → ℝ} (h0 : f 0 = 2)
    (h1 : ∀ x, f (5 + 2 * x) = f (-5 - 4 * x))
    (h2 : ∀ x, f (3 * x - 2) = f (5 - 6 * x)) :
    f 2012 = 2 := by

  have h3 : ∀ y, f y = f (5 - 2 * y) := by
    intro y
    have h4 : f (5 + 2 * ((y - 5) / 2)) = f (-5 - 4 * ((y - 5) / 2)) := by
      apply h1
    have h5 : 5 + 2 * ((y - 5) / 2) = (y : ℝ) := by
      ring
    have h6 : -5 - 4 * ((y - 5) / 2) = (5 - 2 * y : ℝ) := by
      ring
    rw [h5, h6] at h4
    linarith

  have h7 : ∀ y, f y = f (1 - 2 * y) := by
    intro y
    have h8 : f (3 * ((y + 2) / 3) - 2) = f (5 - 6 * ((y + 2) / 3)) := by
      apply h2
    have h9 : 3 * ((y + 2) / 3) - 2 = (y : ℝ) := by
      ring
    have h10 : 5 - 6 * ((y + 2) / 3) = (1 - 2 * y : ℝ) := by
      ring
    rw [h9, h10] at h8
    linarith

  have h11 : ∀ z, f (z + 4) = f z := by
    intro z
    have eq1 : f (5 - 2 * ((1 - z) / 2)) = f (1 - 2 * ((1 - z) / 2)) := by 
      have h10 : f ((1 - z) / 2) = f (5 - 2 * ((1 - z) / 2)) := by 
        have h12 : f ((1 - z) / 2) = f (5 - 2 * ((1 - z) / 2)) := by 
          apply h3
        linarith
      have h11 : f ((1 - z) / 2) = f (1 - 2 * ((1 - z) / 2)) := by 
        have h12 : f ((1 - z) / 2) = f (1 - 2 * ((1 - z) / 2)) := by 
          apply h7
        linarith
      linarith
    have h13 : 5 - 2 * ((1 - z) / 2) = z + 4 := by 
      ring
    have h14 : 1 - 2 * ((1 - z) / 2) = (z : ℝ) := by 
      ring
    rw [h13, h14] at eq1 
    linarith

  have h16 : f 2012 = f (0 : ℝ) := by
    have h17 : ∀ k : ℕ, f ((0 : ℝ) + (k : ℝ) * 4) = f (0 : ℝ) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h19 : (0 : ℝ) + (↑(k + 1 : ℕ) : ℝ) * 4 = (0 : ℝ) + (↑k : ℝ) * 4 + 4 := by
          simp at *
          all_goals
            ring
        rw [h19]
        have h20 : f ((0 : ℝ) + (↑k : ℝ) * 4 + 4) = f ((0 : ℝ) + (↑k : ℝ) * 4) := by
          specialize h11 ((0 : ℝ) + (↑k : ℝ) * 4)
          have h21 : f ((0 : ℝ) + (↑k : ℝ) * 4 + 4) = f ((0 : ℝ) + (↑k : ℝ) * 4) := by
            rw [show (0 : ℝ) + (↑k : ℝ) * 4 + 4 = ((0 : ℝ) + (↑k : ℝ) * 4) + 4 by ring]
            exact h11
          linarith
        have h22 : f ((0 : ℝ) + (↑k : ℝ) * 4) = f (0 : ℝ) := by
          linarith [ih]
        linarith [h20, h22]
    specialize h17 503
    norm_num at h17 ⊢
    linarith 
  linarith [h0, h16]