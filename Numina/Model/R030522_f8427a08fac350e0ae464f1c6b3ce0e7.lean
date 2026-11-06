import Mathlib


theorem algebra_219077 {a b c : ℝ} (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a)
    (h₃ : a * b * c = 1) :
    1 / (a * (a - b) * (a - c)) + 1 / (b * (b - a) * (b - c)) +
    1 / (c * (c - a) * (c - b)) = 1 := by

  have ha1 : a - b ≠ 0 := by
    intro h
    apply h₀
    linarith

  have ha2 : a - c ≠ 0 := by
    intro h
    apply h₂
    linarith

  have hb1 : b - a ≠ 0 := by
    intro h
    apply h₀
    linarith

  have hb2 : b - c ≠ 0 := by
    intro h
    apply h₁
    linarith

  have hc1 : c - a ≠ 0 := by
    intro h
    apply h₂
    linarith

  have hc2 : c - b ≠ 0 := by
    intro h
    apply h₁
    linarith

  have ha0 : a ≠ 0 := by
    by_contra h
    rw [h] at h₃
    have : b * c = 0 := by
      nlinarith
    have : 1 = 0 := by
      nlinarith
    linarith

  have hb0 : b ≠ 0 := by
    by_contra h
    rw [h] at h₃
    have : a * c = 0 := by
      nlinarith
    have : 1 = 0 := by
      nlinarith
    linarith

  have hc0 : c ≠ 0 := by
    by_contra h
    rw [h] at h₃
    have : a * b = 0 := by
      nlinarith
    have : 1 = 0 := by
      nlinarith
    linarith

  have eq1 : 1 / (a * (a - b) * (a - c)) + 1 / (b * (b - a) * (b - c)) + 1 / (c * (c - a) * (c - b)) =
      (b * c * (b - c) - a * c * (a - c) + a * b * (a - b)) / (a * b * c * (a - b) * (a - c) * (b - c)) := by
    field_simp [ha0, hb0, hc0, ha1, ha2, hb1, hb2, hc1, hc2]
    ring

  have eq2 : b * c * (b - c) - a * c * (a - c) + a * b * (a - b) = (a - b) * (a - c) * (b - c) := by
    nlinarith [sq_pos_of_ne_zero (show (a - b) ≠ 0 by exact ha1), sq_pos_of_ne_zero (show (a - c) ≠ 0 by exact ha2), sq_pos_of_ne_zero (show (b - c) ≠ 0 by exact hb2), sq_pos_of_ne_zero (show a ≠ 0 by exact ha0), sq_pos_of_ne_zero (show b ≠ 0 by exact hb0), sq_pos_of_ne_zero (show c ≠ 0 by exact hc0)]

  rw [eq1]

  have h0 : a * b * c * (a - b) * (a - c) * (b - c) ≠ 0 := by
    have ha01 : a ≠ 0 := by
      exact ha0
    have hb01 : b ≠ 0 := by
      exact hb0
    have hc01 : c ≠ 0 := by
      exact hc0
    have ha011 : a - b ≠ 0 := by
      exact ha1
    have ha022 : a - c ≠ 0 := by
      exact ha2
    have hb022 : b - c ≠ 0 := by
      exact hb2
    simp [ha01, hb01, hc01, ha011, ha022, hb022]
    all_goals
      tauto

  have eq3 : (b * c * (b - c) - a * c * (a - c) + a * b * (a - b)) / (a * b * c * (a - b) * (a - c) * (b - c)) = 1 := by
    rw [eq2]
    have h4 : a * b * c = 1 := h₃
    have eq4 : (a - b) * (a - c) * (b - c) = (a - b) * (a - c) * (b - c) := by rfl
    have h00 : a * b * c * (a - b) * (a - c) * (b - c) ≠ 0 := h0
    field_simp [h4, show (a - b) * (a - c) * (b - c) ≠ 0 by
      have ha011 : a - b ≠ 0 := by
        exact ha1
      have ha022 : a - c ≠ 0 := by
        exact ha2
      have hb022 : b - c ≠ 0 := by
        exact hb2
      simp [ha011, ha022, hb022]
    ]
    all_goals
      nlinarith

  exact eq3