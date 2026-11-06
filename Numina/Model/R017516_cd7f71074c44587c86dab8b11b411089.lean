import Mathlib

theorem algebra_102588 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : (a + b + c) / (a + b - c) = 7) (h2 : (a + b + c) / (a + c - b) = 1.75) :
    (a + b + c) / (b + c - a) = 3.5 := by
  have h1' : a + b - c ≠ 0 := by
    by_contra h
    have : (a + b + c) / (a + b - c) = 0 := by
      rw [h]
      norm_num
    linarith
  -- From question 1 cross multiply to get a + b + c = 7(a + b - c)
  have h1_eq : a + b + c = 7 * (a + b - c) := by
    field_simp [h1'] at h1
    linarith
  -- For question 2: cross multiply to 4(a + b + c) = 7(a + c - b)
  have h2' : a + c - b ≠ 0 := by
    by_contra h
    have : (a + b + c) / (a + c - b) = 0 := by
      rw [h]
      norm_num
    norm_num at h2
    all_goals
      linarith
  have h2_eq : a + b + c = 1.75 * (a + c - b) := by
    field_simp [h2'] at h2
    linarith
  have eq1 : 3 * a + 3 * b = 4 * c := by
    linarith
  have eq2 : 4 * (a + b + c) = 7 * (a + c - b) := by
    have h2_eq' : a + b + c = 1.75 * (a + c - b) := h2_eq
    have h3 : (1.75 : ℝ) = (7 / 4 : ℝ) := by norm_num
    rw [h3] at h2_eq'
    linarith
  have h3 : b = 3 / 5 * a := by
    nlinarith
  have h4 : c = 6 / 5 * a := by
    have hc1 : c = 3 / 4 * (a + b) := by
      linarith
    rw [hc1]
    have hb1 : b = 3 / 5 * a := h3
    rw [hb1]
    linarith
  have h5 : a + b + c = 14 / 5 * a := by
    have hb1 : b = 3 / 5 * a := h3
    have hc1 : c = 6 / 5 * a := h4
    linarith
  have h6 : b + c - a = 4 / 5 * a := by
    have hb1 : b = 3 / 5 * a := h3
    have hc1 : c = 6 / 5 * a := h4
    linarith
  have h7 : b + c - a ≠ 0 := by
    by_contra h
    have h8 : a = 0 := by
      nlinarith
    linarith
  have h8 : (a + b + c) / (b + c - a) = 3.5 := by
    rw [h5, h6]
    have ha1 : a ≠ 0 := by linarith
    field_simp [ha1]
    <;> ring
  exact h8