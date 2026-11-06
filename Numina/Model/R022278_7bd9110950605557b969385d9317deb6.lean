import Mathlib

theorem inequalities_101625 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 = 3) :
    3 / 4 ∈ Set.Icc (a / (a + 3) + b / (b + 3) + c / (c + 3)) 1 := by 
  constructor
  · -- Show that a / (a + 3) + b / (b + 3) + c / (c + 3) ≤ 3 / 4
    have h1 : a / (a + 3) + b / (b + 3) + c / (c + 3) ≤ 3 / 4 := by
      have h1 : a / (a + 3) ≤ 1 / 4 + 3 / 16 * (a - 1) := by
        have h2 : a + 3 > 0 := by linarith
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (a - 1)]
      have h2 : b / (b + 3) ≤ 1 / 4 + 3 / 16 * (b - 1) := by
        have h2 : b + 3 > 0 := by linarith
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (b - 1)]
      have h3 : c / (c + 3) ≤ 1 / 4 + 3 / 16 * (c - 1) := by
        have h2 : c + 3 > 0 := by linarith
        apply (div_le_iff₀ (by linarith)).mpr
        nlinarith [sq_nonneg (c - 1)]
      have h4 : a / (a + 3) + b / (b + 3) + c / (c + 3) ≤ 3 / 4 := by
        have h5 : a + b + c ≤ 3 := by
          nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
        linarith [h1, h2, h3, h5]
      linarith
    linarith -- Arithmetic solving
  · -- Show that 3 / 4 ≤ 1
    norm_num