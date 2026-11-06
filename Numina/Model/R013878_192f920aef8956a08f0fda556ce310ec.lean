import Mathlib

theorem algebra_96267 {a r : ℝ} (hr : |r| < 1)
(hsum : ∑' n : ℕ, a * r ^ n = 15) (hsumsq : ∑' n : ℕ, (a * r ^ n) ^ 2 = 45) :
a = 5 := by
  have h1 : ∑' n : ℕ, a * r ^ n = a / (1 - r) := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |r| < 1
      simpa using hr
  have h2 : ∑' n : ℕ, (a * r ^ n) ^ 2 = a^2 / (1 - r^2) := by
    have h : ∑' n : ℕ, (a * r ^ n) ^ 2 = ∑' n : ℕ, a^2 * (r^2) ^ n := by
      congr
      funext n
      ring_nf
    rw [h]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one]
    · ring
    · -- Show that |r^2| < 1
      have h3 : |r ^ 2| < 1 := by
        have h4 : r^2 < 1 := by
          nlinarith [abs_lt.mp hr, sq_nonneg r]
        have h5 : -1 < r^2 := by
          nlinarith [abs_lt.mp hr, sq_nonneg r]
        apply abs_lt.mpr
        constructor <;> nlinarith
      simpa using h3
  rw [h1] at hsum
  rw [h2] at hsumsq
  have h3 : r ≠ 1 := by
    by_contra h
    -- Now r = 1
    have h4 : |r| = 1 := by
      rw [h]
      norm_num [abs]
    have h5 : |r| < (1 : ℝ) := hr
    linarith [h4, h5]
  have eq3 : a = 15 * (1 - r) := by
    have h4 : 1 - r ≠ 0 := by
      by_contra h
      have h3' : r = 1 := by
        linarith
      tauto -- This would use that r ≠ 1 (from h3)
    field_simp [h4] at hsum
    linarith
  have eq4 : 1 - r ^ 2 ≠ 0 := by
    by_contra h
    have h5 : r^2 = 1 := by
      linarith
    have h6 : r = 1 ∨ r = -1 := by
      have : r^2 - 1 = 0 := by linarith
      have : (r - 1) * (r + 1) = 0 := by linarith
      cases (mul_eq_zero.1 this) with
      | inl h1 =>
        left
        linarith
      | inr h2 =>
        right
        linarith
    cases h6 with
    | inl h7 =>
      exfalso
      have h3' : r = 1 := h7
      have h3 : r = 1 := h3'
      tauto
    | inr h8 =>
      exfalso
      -- r=-1 implies |r|=1 which is not less than 1
      have h9 : |r| = 1 := by
        rw [show r = -1 by linarith [h8] ]
        norm_num [abs]
      have h10 : |r| < (1 : ℝ) := hr
      linarith [h9, h10]
  field_simp [eq4] at hsumsq
  rw [show a = 15 * (1 - r) by linarith [eq3] ] at hsumsq
  have hquadratic : (r - 1) * (3 * r - 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp hquadratic) with h7 h8
  · -- Case r - 1 = 0, so r = 1
    have h9 : r = 1 := by linarith
    exfalso
    tauto
  · -- Case 3r - 2 = 0, so r = 2/3
    have h11 : r = 2 / 3 := by linarith
    rw [h11] at eq3
    nlinarith