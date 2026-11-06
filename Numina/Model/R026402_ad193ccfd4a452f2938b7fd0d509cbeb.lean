import Mathlib

theorem algebra_130538 (a : ℝ) :
    (∃ x : ℝ, 12 * x ^ 2 + 48 * x - a + 36 = 0 ∧ (a + 60) * x - 3 * (a - 20) = 0) ↔
    a = -12 ∨ a = 0 ∨ a = 180 := by
  constructor
  · -- Assume there's a real number satisfying both equations; prove disjunction.
    rintro ⟨x, ⟨h₁, h₂⟩⟩
    have eq1 : a = 12 * x ^ 2 + 48 * x + 36 := by linarith
    rw [eq1] at h₂
    have h3 : (x + 1) * (x - 2) * (x + 2) = 0 := by
      nlinarith [h₁, h₂]
    cases' (mul_eq_zero.mp h3) with h4 h5
    cases' (mul_eq_zero.mp h4) with h6 h7
    · -- x + 1 = 0
      have hx1 : x = -1 := by linarith
      have ha1 : a = 0 := by
        rw [hx1] at eq1
        linarith
      simp [ha1]
    · -- x - 2 = 0
      have hx2 : x = 2 := by linarith
      have ha2 : a = 180 := by
        rw [hx2] at eq1
        nlinarith
      simp [ha2]
    · -- x + 2 = 0
      have hx3 : x = -2 := by linarith
      have ha3 : a = -12 := by
        rw [hx3] at eq1
        nlinarith
      simp [ha3]
  · -- Assume a is one of the values; prove existence.
    rintro (ha | ha | ha)
    · -- a = -12
      rw [ha]
      use -2
      constructor <;> norm_num
    · -- a = 0
      rw [ha]
      use -1
      constructor <;> norm_num
    · -- a = 180
      rw [ha]
      use 2
      constructor <;> norm_num