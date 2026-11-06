import Mathlib

theorem algebra_1112 {a : ℝ} {b : ℚ} (h : (a + Real.sqrt 2) / (b - Real.sqrt 2) = 2) :
    ¬(∃ x : ℚ, 2 * a + b = x) := by

  have h1 : b - Real.sqrt 2 ≠ 0 := by
    by_contra h1
    have h2 : (a + Real.sqrt 2) / (b - Real.sqrt 2) = 0 := by
      rw [h1]
      norm_num
    rw [h2] at h
    all_goals norm_num at h

  have h2 : a + Real.sqrt 2 = 2 * (b - Real.sqrt 2) := by
    have h3 : b - Real.sqrt 2 ≠ 0 := h1
    field_simp [h3] at h ⊢
    linarith

  intro h3
  rcases h3 with ⟨x, hx⟩

  have h3 : (2 * a + (b : ℝ)) = (x : ℝ) := by
    exact_mod_cast hx

  have h4 : a = 2 * (b : ℝ) - 3 * Real.sqrt 2 := by
    have h2' : a + Real.sqrt 2 = 2 * (b - Real.sqrt 2) := h2
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  have h5 : (2 * a + (b : ℝ)) = 5 * (b : ℝ) - 6 * Real.sqrt 2 := by
    rw [h4]
    nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]

  rw [h5] at h3

  have h6 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)

  have h7 : (5 * (b : ℝ) - (x : ℝ)) ^ 2 = 72 := by
    have h8 : (5 * (b : ℝ) - (x : ℝ)) = 6 * Real.sqrt 2 := by
      nlinarith [Real.sqrt_pos.mpr (show (0:ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    rw [h8]
    have h9 : (6 * Real.sqrt 2) ^ 2 = 72 := by
      calc
        (6 * Real.sqrt 2) ^ 2 = 36 * (Real.sqrt 2) ^ 2 := by ring
        _ = 36 * (2 : ℝ) := by rw [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)]
        _ = (72 : ℝ) := by norm_num
    linarith

  have h9 : (5 * (b : ℚ) - (x : ℚ)) ^ 2 = (72 : ℚ) := by
    have h7' : (5 * (b : ℝ) - (x : ℝ)) ^ 2 = (72 : ℝ) := h7
    exact_mod_cast h7'

  have h10 : ¬ IsSquare (72 : ℚ) := by
    native_decide

  have h11 : IsSquare (72 : ℚ) := by
    have h12 : (5 * (b : ℚ) - (x : ℚ)) ^ 2 = (72 : ℚ) := h9
    have : IsSquare ((72 : ℚ)) := by
      have h12' : (72 : ℚ) = (5 * (b : ℚ) - (x : ℚ)) ^ 2 := by
        linarith
      rw [h12']
      exact IsSquare_sq (5 * (b : ℚ) - (x : ℚ))
    assumption

  contradiction