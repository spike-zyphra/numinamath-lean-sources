import Mathlib

theorem inequalities_296808 (a : ℝ) (ha : ∀ b, |b| < 3 → a < b) :
    a ≤ -3 := by
  by_contra h
  push_neg at h
  have ha0 := ha 0 (by norm_num)
  have h1 : a < (0 : ℝ) := by simpa using ha0
  have ha1 := ha 1 (by norm_num)
  have h2 : a < (1 : ℝ) := by simpa using ha1
  have ha2 := ha (-3 + (a + 3) / 4) (by
    have h2 : a > -3 := by linarith
    have h3 : -3 + (a + 3) / 4 > -3 := by
      linarith
    have h4 : -3 + (a + 3) / 4 < 3 := by
      nlinarith
    apply abs_lt.mpr
    constructor <;> nlinarith
  )
  have h3 : a < -3 + (a + 3) / 4 := by
    simpa using ha2
  nlinarith