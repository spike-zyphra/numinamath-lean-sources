import Mathlib

theorem algebra_136453 {f : ℝ → ℝ} (h₁ : f 1 = 1 / 4) (h₂ : ∀ x y, 4 * f x * f y = f (x + y) + f (x - y)) :
    f 2019 = -1 / 2 := by

  have f0 : f 0 = 1 / 2 := by
    have h3 : 4 * f 1 * f 0 = f (1 + 0) + f (1 - 0) := h₂ 1 0
    norm_num [h₁] at h3
    linarith

  have h3 : ∀ (x : ℝ), f (x + 6) = f x := by
    intro x
    have eq7 : 4 * f (x + 1) * f 1 = f (x + 2) + f x := by
      have eq1 : 4 * f (x + 1) * f 1 = f (x + 1 + 1) + f (x + 1 - 1) := h₂ (x + 1) 1
      have h8 : (x + 1 : ℝ) + 1 = x + 2 := by ring
      have h9 : (x + 1 : ℝ) - 1 = x := by ring
      rw [h8, h9] at eq1
      linarith

    have eq8 : 4 * f (x + 2) * f 1 = f (x + 3) + f (x + 1) := by
      have eq2 : 4 * f (x + 2) * f 1 = f (x + 2 + 1) + f (x + 2 - 1) := h₂ (x + 2) 1
      have h8 : (x + 2 : ℝ) + 1 = x + 3 := by ring
      have h9 : (x + 2 : ℝ) - 1 = x + 1 := by ring
      rw [h8, h9] at eq2
      linarith

    have eq9 : 4 * f (x + 3) * f 1 = f (x + 4) + f (x + 2) := by
      have eq3 : 4 * f (x + 3) * f 1 = f (x + 3 + 1) + f (x + 3 - 1) := h₂ (x + 3) 1
      have h8 : (x + 3 : ℝ) + 1 = x + 4 := by ring
      have h9 : (x + 3 : ℝ) - 1 = x + 2 := by ring
      rw [h8, h9] at eq3
      linarith

    have eq10 : 4 * f (x + 4) * f 1 = f (x + 5) + f (x + 3) := by
      have eq4 : 4 * f (x + 4) * f 1 = f (x + 4 + 1) + f (x + 4 - 1) := h₂ (x + 4) 1
      have h8 : (x + 4 : ℝ) + 1 = x + 5 := by ring
      have h9 : (x + 4 : ℝ) - 1 = x + 3 := by ring
      rw [h8, h9] at eq4
      linarith

    have eq11 : 4 * f (x + 5) * f 1 = f (x + 6) + f (x + 4) := by
      have eq5 : 4 * f (x + 5) * f 1 = f (x + 5 + 1) + f (x + 5 - 1) := h₂ (x + 5) 1
      have h8 : (x + 5 : ℝ) + 1 = x + 6 := by ring
      have h9 : (x + 5 : ℝ) - 1 = x + 4 := by  ring
      rw [h8, h9] at eq5
      linarith

    rw [h₁] at eq7 eq8 eq9 eq10 eq11
    nlinarith [eq7, eq8, eq9, eq10, eq11]

  have h4 : f 2019 = f (3 : ℝ) := by

    have h5 : ∀ (k : ℕ), f (3 + (k : ℝ) * 6) = f (3 : ℝ) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h10 : (3 + ((k + 1 : ℕ) : ℝ) * 6) = (3 + ((k : ℕ) : ℝ) * 6) + 6 := by
          simp at *
          ring_nf
        rw [h10]
        have h11 : f ((3 + ((k : ℕ) : ℝ) * 6) + 6) = f (3 + ((k : ℕ) : ℝ) * 6) := by
          apply h3
        linarith [h11, ih]

    specialize h5 336
    norm_num at h5 ⊢
    linarith [h5]

  have h5 : f (3 : ℝ) = -1 / 2 := by

    have eq2 : f (2 : ℝ) = -1/4 := by
      have eq1 : 4 * f (1 : ℝ) * f 1 = f (2 : ℝ) + f (0 : ℝ) := by
        specialize h₂ 1 1
        norm_num at h₂ ⊢
        linarith
      rw [h₁, f0] at eq1
      nlinarith

    have eq3 : 4 * f (2 : ℝ) * f 1 = f (3 : ℝ) + f (1 : ℝ) := by
      specialize h₂ 2 1
      norm_num at h₂ ⊢
      linarith

    rw [h₁, eq2] at eq3
    nlinarith

  linarith [h4, h5]