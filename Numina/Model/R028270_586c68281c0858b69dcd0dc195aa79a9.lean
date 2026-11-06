import Mathlib

theorem algebra_20931 {A B C : ℤ} (h : ∀ x : ℝ, x ≠ -2 → (x + A) / (B * x + C) = (-x + 4) / (x - 2)) (h1 : B * (4 : ℝ) + C ≠ 0) (h2 : (C : ℝ) ≠ 0) (h3 : B * (3 : ℝ) + C ≠ 0) :
    A + B + C = -3 := by

  have eq1 := h 0 (by norm_num)
  have eq4 : (B * (0 : ℝ) + (C : ℝ)) ≠ 0 := by
    have hc : (C : ℝ) ≠ 0 := h2
    have : (B * (0 : ℝ) + (C : ℝ)) = (C : ℝ) := by ring
    rw [this]
    exact hc

  have eq5 : (0 + (A : ℝ)) / (B * (0 : ℝ) + (C : ℝ)) = (-0 + 4) / (0 - 2 : ℝ) := by
    simpa using eq1

  have eq6 : (0 + (A : ℝ)) / (B * (0 : ℝ) + (C : ℝ)) = -2 := by
    rw [eq5]
    norm_num

  have eq8 : (0 + (A : ℝ)) = -2 * (B * (0 : ℝ) + (C : ℝ)) := by
    have hne : (B * (0 : ℝ) + (C : ℝ)) ≠ 0 := eq4
    field_simp [hne] at eq6 ⊢
    linarith

  have eq9 : (A : ℝ) = -2 * (C : ℝ) := by
    ring_nf at eq8 ⊢
    linarith

  have eq9' : A = -2 * C := by
    exact_mod_cast eq9

  have eq10 := h 4 (by norm_num)
  have eq11 : (B * (4 : ℝ) + (C : ℝ)) ≠ 0 := h1
  have eq13 : (4 + (A : ℝ)) / (B * (4 : ℝ) + (C : ℝ)) = (0 : ℝ) := by
    have eq13' : (4 + (A : ℝ)) / (B * (4 : ℝ) + (C : ℝ)) = (- (4 : ℝ) + 4) / ((4 : ℝ) - 2) := by
      simpa using eq10
    rw [eq13']
    norm_num

  have eq16 : (4 + (A : ℝ)) = 0 := by
    have hne : (B * (4 : ℝ) + (C : ℝ)) ≠ 0 := h1
    field_simp [hne] at eq13 ⊢
    linarith

  have eq17 : (A : ℝ) = -4 := by
    linarith

  have eq17' : A = -4 := by
    exact_mod_cast eq17

  have eq18' : C = 2 := by
    rw [show A = -4 by linarith [eq17']] at eq9'
    omega

  have eq20 := h 3 (by norm_num)
  have eq21 : (B * (3 : ℝ) + (C : ℝ)) ≠ 0 := h3
  have eq22 : (3 + (A : ℝ)) / (B * (3 : ℝ) + (C : ℝ)) = (1 : ℝ) := by
    have eq23 : (3 + (A : ℝ)) / (B * (3 : ℝ) + (C : ℝ)) = (- (3 : ℝ) + 4) / ((3 : ℝ) - 2) := by
      simpa using eq20
    rw [eq23]
    norm_num

  have eq24 : (3 + (A : ℝ)) = (B * (3 : ℝ) + (C : ℝ)) := by
    have hne : (B * (3 : ℝ) + (C : ℝ)) ≠ 0 := h3
    field_simp [hne] at eq22 ⊢
    linarith

  have eq25 : (A : ℝ) = -4 := by
    exact_mod_cast eq17'

  have eq26 : (C : ℝ) = 2 := by
    have hc : (C : ℝ) = 2 := by
      exact_mod_cast (show (C : ℤ) = 2 by linarith [eq18'])
    linarith

  have eq27 : (B : ℝ) = -1 := by
    rw [eq25, eq26] at eq24
    linarith

  have eq28 : B = -1 := by
    exact_mod_cast eq27

  omega