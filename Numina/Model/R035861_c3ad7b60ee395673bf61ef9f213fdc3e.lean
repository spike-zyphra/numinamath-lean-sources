import Mathlib

open Real

theorem calculus_12021 :
   {(a, b) : ℝ × ℝ | ∀ θ, cos θ ^ 3 = a * cos (3 * θ) + b * cos θ } = {(1 / 4, 3 / 4)} := by
  ext ⟨a, b⟩
  simp [-one_div]
  constructor
  · -- Assume that for all θ, cos^3 θ = a * cos (3 * θ) + b * cos θ, prove (a, b) = (1/4, 3/4)
    intro h
    have h1 := h 0
    have h_eq1 : a + b = 1 := by
      have h0 : cos (0 : ℝ) ^3 = a * cos (3 * (0 : ℝ)) + b * cos (0 : ℝ) := by simpa using h1
      simp [cos_zero] at h0
      linarith
    have h2 := h (Real.pi / 3)
    have h_eq2 : - a + b / 2 = 1 / 8 := by
      have h2' : cos (Real.pi / 3 : ℝ) ^3 = a * cos (3 * (Real.pi / 3 : ℝ)) + b * cos (Real.pi / 3 : ℝ) := by simpa using h2
      have hcos1 : cos (Real.pi / 3 : ℝ) = 1 / 2 := by
        exact cos_pi_div_three
      have hcos3 : cos (3 * (Real.pi / 3 : ℝ)) = -1 := by
        have h1 : 3 * (Real.pi / 3 : ℝ) = Real.pi := by ring
        rw [h1]
        norm_num
        all_goals linarith
      rw [hcos1, hcos3] at h2'
      linarith
    have ha1 : a = 1 / 4 := by
      nlinarith
    have hb1 : b = 3 / 4 := by
      linarith
    simp [ha1, hb1]
  · -- Show that (1/4, 3/4) satisfies the equation
    rintro ⟨rfl, rfl⟩
    intro θ
    have hcos3 : cos (3 * θ) = 4 * cos θ ^3 - 3 * cos θ := by
      rw [cos_three_mul]
    rw [hcos3]
    ring