import Mathlib

theorem algebra_199978 {x : ℝ} (hx : x ≠ 0) :
    1 / (2 + 1 / (3 + 1 / (4 + 1 / (5 + 1 / x)))) = 16 / 37 ↔ x = -0.25 := by
  constructor
  · -- Forward direction: Equation implies x = -0.25 
    intro h
    have h1 : x ≠ 0 := hx
    have eq1 : 1 / (2 + 1 / (3 + 1 / (4 + 1 / (5 + 1 / x)))) = 16 / 37 := h
    have eq2 : 5 + 1 / x = (5 * x + 1) / x := by 
      field_simp [h1]
      <;> ring
    have eq3 : 4 + 1 / (5 + 1 / x) = (21 * x + 4) / (5 * x + 1) := by 
      rw [eq2]
      field_simp [(show 5 * x + 1 ≠ 0 by 
        by_contra h'
        have : x = -1 / 5 := by linarith
        rw [this] at eq1
        norm_num at eq1
      ), (show x ≠ 0 by exact h1)]
      <;> ring
    have eq4 : 3 + 1 / (4 + 1 / (5 + 1 / x)) = (68 * x + 13) / (21 * x + 4) := by 
      rw [eq3]
      field_simp [(show 21 * x + 4 ≠ 0 by 
        by_contra h'
        have : x = -4 / 21 := by linarith
        rw [this] at eq1
        norm_num at eq1
      ), (show 5 * x + 1 ≠ 0 by 
        by_contra h'
        have : x = -1 / 5 := by linarith
        rw [this] at eq1
        norm_num at eq1
      )]
      <;> ring
    have eq5 : 2 + 1 / (3 + 1 / (4 + 1 / (5 + 1 / x))) = (157 * x + 30) / (68 * x + 13) := by 
      rw [eq4]
      field_simp [(show 68 * x + 13 ≠ 0 by 
        by_contra h'
        have : x = -13 / 68 := by linarith
        rw [this] at eq1
        norm_num at eq1
      ), (show 21 * x + 4 ≠ 0 by 
        by_contra h'
        have : x = -4 / 21 := by linarith
        rw [this] at eq1
        norm_num at eq1
      )]
      <;> ring
    have eq6 : 1 / (2 + 1 / (3 + 1 / (4 + 1 / (5 + 1 / x)))) = (68 * x + 13) / (157 * x + 30) := by
      rw [eq5]
      field_simp [(show 157 * x + 30 ≠ 0 by 
        by_contra h'
        have : x = -30 / 157 := by linarith
        rw [this] at eq1
        norm_num at eq1
      ), (show 68 * x + 13 ≠ 0 by 
        by_contra h'
        have : x = -13 / 68 := by linarith
        rw [this] at eq1
        norm_num at eq1
      )]
      <;> ring
    rw [eq6] at eq1
    have eq7 : 37 * (68 * x + 13) = 16 * (157 * x + 30) := by
      field_simp [(show 157 * x + 30 ≠ 0 by 
        by_contra h'
        have : x = -30 / 157 := by linarith
        rw [this] at eq1
        norm_num at eq1
      ), (show 68 * x + 13 ≠ 0 by 
        by_contra h'
        have : x = -13 / 68 := by linarith
        rw [this] at eq1
        norm_num at eq1
      )] at eq1 ⊢
      linarith
    have eq8 : 4 * x = -1 := by
      nlinarith
    have eq9 : x = -1 / 4 := by
      linarith
    rw [eq9]
    norm_num
  · -- Backward direction: x = -0.25 implies equation
    intro h
    have h2 : x = -1 / 4 := by
      rw [h]
      norm_num
    rw [h2]
    norm_num