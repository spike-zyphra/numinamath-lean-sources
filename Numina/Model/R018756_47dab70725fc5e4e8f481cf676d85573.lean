import Mathlib

theorem algebra_135762 (x y : ℝ) (hx : x ≠ -y) :
    4 / (x + y) = 1 / x + 1 / y ↔ y = x ∧ x ≠ 0 := by
  constructor
  · -- Assume the equation holds, prove the equivalent condition
    intro h
    have h1 : x + y ≠ 0 := by
      intro h2
      apply hx
      linarith
    have h2 : x ≠ 0 := by
      by_contra h2
      have eq1 : x = 0 := h2
      rw [eq1] at h
      -- If x = 0, h becomes: 4 / (0 + y) = 1 / 0 + 1 / y
      -- which simplifies to 4 / y = 0 + 1 / y, so 4 / y = 1 / y
      have eq2 : 4 / y = 1 / y := by
        norm_num at h ⊢
        all_goals try linarith
      have h_eq6 : y ≠ 0 := by
        intro h_eq0
        have h3 : x + y = 0 := by
          linarith [eq1, h_eq0]
        contradiction
      -- From 4 / y = 1 / y and y ≠ 0, we can derive a contradiction
      have eq3 : 4 = 1 := by
        field_simp [h_eq6] at eq2 ⊢
        all_goals linarith
      linarith
    have h3 : y ≠ 0 := by
      by_contra h4
      have eq4 : y = 0 := h4
      have eq5 : x + y = x := by 
        linarith [eq4]
      have eq6 : x ≠ 0 := by
        intro eq7
        have eq8 : x + y = 0 := by 
          linarith [eq4, eq7]
        contradiction
      have eq3 : 4 / x = 1 / x := by 
        rw [eq4] at h
        norm_num at h ⊢
        all_goals try linarith
      have eq4 : 4 = 1 := by
        field_simp [eq6] at eq3 ⊢
        all_goals linarith
      linarith
    have h4 : 4 * x * y = y * (x + y) + x * (x + y) := by
      field_simp [h1, h2, h3] at h ⊢
      nlinarith
    have h5 : (x - y) ^ 2 = 0 := by
      nlinarith
    have h6 : x - y = 0 := by
      apply pow_eq_zero 
      exact h5
    have h7 : x = y := by linarith
    exact ⟨show y = x by linarith, h2⟩
  · -- Assume the equivalent condition holds, prove the equation
    rintro ⟨h_eq, hx1⟩
    have h1 : x + y = 2 * x := by
      have : y = x := h_eq
      linarith
    have h2 : x ≠ 0 := hx1
    have h3 : y ≠ 0 := by
      intro hy
      apply h2
      linarith [h_eq, hy]
    have h4 : x + y ≠ 0 := by
      have : x + y = 2 * x := h1
      rw [this]
      intro h5
      have : x = 0 := by linarith
      contradiction
    have h5 : 4 * x * y = y * (x + y) + x * (x + y) := by
      rw [show y = x by linarith [h_eq]]
      nlinarith [sq_pos_of_ne_zero (show x ≠ 0 by exact h2), sq_nonneg (x)]
    field_simp [h4, h2, h3]
    <;> nlinarith [h5]