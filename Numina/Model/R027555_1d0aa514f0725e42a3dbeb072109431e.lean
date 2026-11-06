import Mathlib

theorem algebra_2954
  {a b c x y z : ℝ}
  (h₀ : a ≠ 0)
  (h₁ : b ≠ 0)
  (h₂ : c ≠ 0)
  (h₃ : x ≠ 0)
  (h₄ : y ≠ 0)
  (h₅ : z ≠ 0)
  (h₆ : x^2 * (y + z) / a^3 = 1)
  (h₇ : y^2 * (x + z) / b^3 = 1)
  (h₈ : z^2 * (y + x) / c^3 = 1)
  (h₉ : x * y * z / (a * b * c) = 1) :
  a^3 + b^3 + c^3 + a * b * c = 0 := by

  have eq1 : x^2 * (y + z) = a^3 := by
    have h6' : x^2 * (y + z) / a^3 = 1 := h₆
    have ha3 : a^3 ≠ 0 := by
      intro ha30
      have : a = 0 := by
        have h10 : a^3 = 0 := by linarith
        simp at h10 ⊢
        all_goals tauto
      tauto
    field_simp [ha3] at h6' ⊢
    all_goals nlinarith

  have eq2 : y^2 * (x + z) = b^3 := by
    have h7' : y^2 * (x + z) / b^3 = 1 := h₇
    have hb3 : b^3 ≠ 0 := by
      intro hb30
      have : b = 0 := by
        have h10 : b^3 = 0 := by linarith
        simp at h10 ⊢
        all_goals tauto
      tauto
    field_simp [hb3] at h7' ⊢
    all_goals nlinarith

  have eq3 : z^2 * (y + x) = c^3 := by
    have h8' : z^2 * (y + x) / c^3 = 1 := h₈
    have hc3 : c^3 ≠ 0 := by
      intro hc30
      have : c = 0 := by
        have h10 : c^3 = 0 := by linarith
        simp at h10 ⊢
        all_goals tauto
      tauto
    field_simp [hc3] at h8' ⊢
    all_goals nlinarith

  have eq4 : x * y * z = a * b * c := by
    have h9' : x * y * z / (a * b * c) = 1 := h₉
    have h10 : a * b * c ≠ 0 := by
      apply mul_ne_zero
      apply mul_ne_zero
      exact h₀
      exact h₁
      exact h₂
    field_simp [h10] at h9' ⊢
    all_goals nlinarith

  have eq5 : a * b * c = (y + z) * (x + z) * (y + x) := by
    have h11 : (x * y * z) ^ 2 * ((y + z) * (x + z) * (y + x)) = a^3 * b^3 * c^3 := by
      calc
        (x * y * z) ^ 2 * ((y + z) * (x + z) * (y + x)) = x^2 * y^2 * z^2 * ((y + z) * (x + z) * (y + x)) := by ring
        _ = x^2 * (y + z) * y^2 * (x + z) * z^2 * (y + x) := by ring
        _ = (x^2 * (y + z)) * (y^2 * (x + z)) * (z^2 * (y + x)) := by ring
        _ = (a^3) * (b^3) * (c^3) := by rw [eq1, eq2, eq3]
        _ = a^3 * b^3 * c^3 := by ring
    have h14 : (a * b * c) ^ 2 * ((y + z) * (x + z) * (y + x)) = (a * b * c) ^ 3 := by
      rw [show (a * b * c) ^ 2 = (x * y * z) ^ 2 by
        have h15 : x * y * z = a * b * c := by linarith [eq4]
        rw [h15]
      ] at *
      nlinarith [sq_pos_of_ne_zero (show a ≠ 0 by exact h₀), sq_pos_of_ne_zero (show b ≠ 0 by exact h₁), sq_pos_of_ne_zero (show c ≠ 0 by exact h₂), sq_pos_of_ne_zero (show x ≠ 0 by exact h₃), sq_pos_of_ne_zero (show y ≠ 0 by exact h₄), sq_pos_of_ne_zero (show z ≠ 0 by exact h₅)]
    have h15 : (y + z) * (x + z) * (y + x) = a * b * c := by
      have h16 : (a * b * c) ^ 2 ≠ 0 := by
        have h17 : a * b * c ≠ 0 := by
          apply mul_ne_zero
          apply mul_ne_zero
          exact h₀
          exact h₁
          exact h₂
        have h18 : (a * b * c) ^ 2 ≠ 0 := by
          apply pow_ne_zero 2
          exact h17
        assumption
      have h19 : (y + z) * (x + z) * (y + x) = a * b * c := by
        apply (mul_left_inj' h16).mp
        linarith
      assumption
    linarith

  have eq7 : a ^ 3 + b ^ 3 + c ^ 3 = - (a * b * c) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_pos_of_ne_zero h₀, sq_pos_of_ne_zero h₁, sq_pos_of_ne_zero h₂, sq_pos_of_ne_zero h₃, sq_pos_of_ne_zero h₄, sq_pos_of_ne_zero h₅]

  -- need to show a^3 + b^3 + c^3 + abc = 0
  linarith [eq7, eq5]