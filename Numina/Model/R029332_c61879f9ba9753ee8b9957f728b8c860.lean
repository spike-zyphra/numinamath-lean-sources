import Mathlib

theorem algebra_1350
    {a : ℤ} (ha : a > 0)
    (x y : ℝ)
    (h1 : a * x + 4 * y = 8)
    (h2 : 3 * x + 2 * y = 6)
    (hx : x > 0) (hy : y < 0) :
    a = 5 := by

  have eq1 : x = 4 / (6 - (a : ℝ)) := by
    have eq2 : (6 - (a : ℝ)) * x = 4 := by
      have eq3 : (a : ℝ) * x + 4 * y = 8 := by exact_mod_cast h1
      have eq4 : 3 * x + 2 * y = 6 := by exact_mod_cast h2
      have eq5 : (6 * x + 4 * y) = 12 := by
        linarith [eq4]
      nlinarith [eq3, eq5]
    have hne : (6 - (a : ℝ)) ≠ 0 := by
      by_contra h
      have h0 : (6 - (a : ℝ)) = 0 := by linarith
      rw [h0] at eq2
      nlinarith
    field_simp [hne]
    all_goals nlinarith
  have h3 : (6 - (a : ℝ)) > 0 := by
    have hx2 : x > 0 := hx
    rw [eq1] at hx2
    apply div_pos_iff.mp at hx2
    cases hx2 with
    | inl h =>
      linarith
    | inr h =>
      nlinarith
  have eq2 : y = 3 - 6 / (6 - (a : ℝ)) := by
    have eq3 : 3 * x + 2 * y = 6 := by exact_mod_cast h2
    rw [eq1] at eq3
    field_simp [(show (6 - (a : ℝ)) ≠ 0 by 
      by_contra h
      have h0 : (6 - (a : ℝ)) = 0 := by linarith
      rw [h0] at h3
      nlinarith
    )] at *
    linarith
  have h4 : (3 - 6 / (6 - (a : ℝ)) : ℝ) < 0 := by
    nlinarith [hy, eq2]
  have h5 : (a : ℝ) > 4 := by
    by_contra h
    push_neg at h
    have h8 : (6 / (6 - (a : ℝ)) : ℝ) ≤ 3 := by
      have h9 : (6 - (a : ℝ)) ≥ 2 := by
        have ha2 : (a : ℝ) ≤ 4 := by exact_mod_cast h
        nlinarith
      apply (div_le_iff₀ (by linarith)).mpr
      nlinarith
    nlinarith
  have h6 : a > 4 := by
    by_contra h
    push_neg at h
    have h7 : (a : ℝ) ≤ (4 : ℝ) := by exact_mod_cast h
    nlinarith
  have h7 : a < 6 := by
    by_contra h
    push_neg at h
    have h8 : (a : ℝ) ≥ (6 : ℝ) := by exact_mod_cast h
    nlinarith
  have h9 : a = 5 := by
    linarith
  exact_mod_cast h9