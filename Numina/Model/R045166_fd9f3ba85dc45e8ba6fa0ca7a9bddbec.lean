import Mathlib

theorem algebra_309976 {a b c d : ℝ} (h1 : a * b + c + d = 3) (h2 : b * c + d + a = 5) (h3 : c * d + a + b = 2) (h4 : d * a + b + c = 6) :
    a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 3 := by

  have eq5 : (b - 1) * (c - a) = 2 := by
    nlinarith

  have eq6 : (b - d) * (c - 1) = 3 := by
    nlinarith

  have eq7 : (c - a) * (d - 1) = -4 := by
    nlinarith

  have eq8 : d = 3 - 2 * b := by
    have h5 : b - 1 ≠ 0 := by
      by_contra h
      have hb1 : b - 1 = 0 := by linarith [h]
      rw [hb1] at eq5
      nlinarith
    have h8 : 2 * (d - 1) = -4 * (b - 1) := by
      have h9 : (c - a) = 2 / (b - 1) := by
        field_simp [show b - 1 ≠ 0 by 
          exact h5
        ]
        nlinarith [eq5]
      rw [h9] at eq7
      field_simp [show b - 1 ≠ 0 by 
        exact h5
      ] at eq7 ⊢
      nlinarith
    linarith

  have eq9 : (b - 1) * (c - 1) = 1 := by
    rw [show d = 3 - 2 * b by linarith [eq8]] at eq6
    nlinarith

  have eq10 : a = 2 - c := by
    have h5 : b - 1 ≠ 0 := by 
      by_contra h
      have hb1 : b - 1 = 0 := by linarith [h]
      rw [hb1] at eq5
      nlinarith
    have h6 : (c - a) = 2 * (c - 1) := by
      have h7 : (b - 1) * (c - a) = 2 := by linarith [eq5]
      have h8 : (b - 1) * (c - 1) = 1 := by linarith [eq9]
      have h9 : c - a = 2 * (c - 1) := by
        apply (mul_left_inj' (show b - 1 ≠ 0 by
          exact h5
        )).mp
        nlinarith
      linarith
    nlinarith

  have eq11 : c * (1 - b) = 0 := by
    rw [show a = 2 - c by linarith [eq10], show d = 3 - 2 * b by linarith [eq8]] at h1
    nlinarith

  cases' (mul_eq_zero.mp eq11) with hc hb
  · -- Case where $c = 0$.
    have hc0 : c = 0 := by linarith
    have ha2 : a = 2 := by linarith [eq10, hc0]
    have hb0 : b = 0 := by
      rw [show c = (0 : ℝ) by linarith [hc0]] at eq9
      have h15 : (b - 1) * (-1) = 1 := by nlinarith
      nlinarith
    have hd3 : d = 3 := by linarith [eq8, hb0]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  · -- Case where $b = 1$.
    have hb1 : b = 1 := by linarith
    rw [show b = (1 : ℝ) by linarith [hb1]] at eq9
    nlinarith