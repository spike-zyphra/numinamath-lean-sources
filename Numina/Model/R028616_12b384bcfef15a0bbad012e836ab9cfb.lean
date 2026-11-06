import Mathlib

theorem algebra_95135 : let isValid (a d r : ℝ) := (a = 9) ∧ (a + d + 2 = r * a ∧ a + 2 * d + 20 = r * (a + d + 2));
((isValid a d r) → a + 2*d + 20 ≥ 1) ∧ (∃ a d r, (isValid a d r) ∧  a + 2*d + 20 = 1) := by
  intro isValid
  constructor
  · -- Assume (isValid a d r), prove a + 2*d + 20 ≥ 1
    intro h
    rcases h with ⟨ha, ⟨h1, h2⟩⟩
    rw [ha] at h1 h2
    have eq1 : 11 + d = 9 * r := by
      linarith 
    have eq2 : 29 + 2 * d = r * (11 + d) := by
      nlinarith 
    have h3 : r = (11 + d) / 9 := by
      linarith [eq1]
    rw [h3] at eq2
    have h4 : 9 * (29 + 2 * d) = (11 + d) ^ 2 := by
      nlinarith 
    have : (d - 10) * (d + 14) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp this) with h5 h6
    · -- Case d = 10
      have d_eq_10 : d = 10 := by linarith 
      nlinarith [d_eq_10]
    · -- Case d = -14
      have d_eq : d = -14 := by linarith 
      nlinarith [d_eq]
  · -- Show existence
    use 9
    use -14
    use -1 / 3
    constructor
    · -- Show that (isValid 9 (-14) (-1 / 3))
      constructor
      · -- a = 9
        norm_num 
      constructor
      · -- Show that a + d + 2 = r * a
        norm_num
      · -- Show that a + 2 * d + 20 = r * (a + d + 2)
        norm_num 
    · -- Show that a + 2 * d + 20 = 1
      norm_num