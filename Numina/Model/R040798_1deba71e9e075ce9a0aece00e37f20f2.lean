import Mathlib

theorem algebra_242973 {x y z : ℝ} (h1 : x + y + 2 - 4 * x * y = 0) (h2 : y + z + 2 - 4 * y * z = 0)
    (h3 : z + x + 2 - 4 * z * x = 0) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = -1 / 2 ∧ y = -1 / 2 ∧ z = -1 / 2) := by

  have h4 : (2 * x - 1 / 2) * (2 * y - 1 / 2) = 9 / 4 := by
    nlinarith
  have h5 : (2 * y - 1 / 2) * (2 * z - 1 / 2) = 9 / 4 := by
    nlinarith
  have h6 : (2 * z - 1 / 2) * (2 * x - 1 / 2) = 9 / 4 := by
    nlinarith

  have h8 : 2 * x - 1 / 2 = 2 * z - 1 / 2 := by
    by_cases h : (2 * y - 1 / 2) = 0
    · -- Assume $2y - 1/2 = 0$
      have h9 : (2 * x - 1 / 2) * (2 * y - 1 / 2) = 0 := by
        rw [h]
        norm_num
      have h10 : (2 * x - 1 / 2) * (2 * y - 1 / 2) = 9 / 4 := by
        nlinarith
      linarith
    · -- Assume $2y - 1/2 \neq 0$
      have h4' : (2 * x - 1 / 2) * (2 * y - 1 / 2) = (2 * y - 1 / 2) * (2 * z - 1 / 2) := by
        linarith [h4, h5]
      have h9 : (2 * x - 1 / 2) = (2 * z - 1 / 2) := by
        apply (mul_left_inj' h).mp
        linarith
      linarith

  have h10 : (2 * y - 1 / 2) = (2 * x - 1 / 2) := by
    by_cases h' : (2 * z - 1 / 2) = 0
    · -- Assume $2z - 1/2 = 0$
      have h11 : (2 * y - 1 / 2) * (2 * z - 1 / 2) = 0 := by
        rw [h']
        norm_num
      have h12 : (2 * y - 1 / 2) * (2 * z - 1 / 2) = 9 / 4 := by
        nlinarith
      linarith
    · -- Assume $2z - 1/2 \neq 0$
      have h13 : (2 * y - 1 / 2) * (2 * z - 1 / 2) = (2 * z - 1 / 2) * (2 * x - 1 / 2) := by
        linarith [h5, h6]
      have h14 : (2 * y - 1 / 2) = (2 * x - 1 / 2) := by
        apply (mul_left_inj' h').mp
        linarith
      linarith

  have h12 : (2 * x - 1 / 2) ^ 2 = 9 / 4 := by
    have h13 : (2 * x - 1 / 2) = (2 * y - 1 / 2) := by linarith [h10]
    have h14 : (2 * x - 1 / 2) * (2 * y - 1 / 2) = 9 / 4 := by
      nlinarith
    rw [h13] at h14
    nlinarith

  have h13 : 2 * x - 1 / 2 = 3 / 2 ∨ 2 * x - 1 / 2 = -3 / 2 := by
    have h14 : (2 * x - 1 / 2) ^ 2 = 9 / 4 := h12
    have h15 : (2 * x - 1 / 2) = 3 / 2 ∨ (2 * x - 1 / 2) = -3 / 2 := by
      have h14' : (2 * x - 1 / 2) ^ 2 - 9 / 4 = 0 := by linarith
      have h16 : (2 * x - 1 / 2 - 3 / 2) * (2 * x - 1 / 2 + 3 / 2) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h16) with
      | inl h17 =>
        left
        linarith
      | inr h18 =>
        right
        linarith
    tauto

  cases h13 with
  | inl h14 =>
    have hx1 : x = 1 := by
      nlinarith
    have hy1 : y = 1 := by
      nlinarith [show (2 * y - 1 / 2) = (2 * x - 1 / 2) from by linarith [h10]]
    have hz1 : z = 1 := by
      nlinarith [show (2 * z - 1 / 2) = (2 * x - 1 / 2) from by nlinarith [h8, h10]]
    left
    tauto
  | inr h14 =>
    have hx2 : x = -1 / 2 := by
      nlinarith
    have hy2 : y = -1 / 2 := by
      nlinarith [show (2 * y - 1 / 2) = (2 * x - 1 / 2) from by linarith [h10]]
    have hz2 : z = -1 / 2 := by
      nlinarith [show (2 * z - 1 / 2) = (2 * x - 1 / 2) from by nlinarith [h8, h10]]
    right
    tauto