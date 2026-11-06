import Mathlib

theorem algebra_267141 {x y z : ℝ}
    (h₀ : x ≠ -y) (h₁ : y ≠ -z) (h₂ : z ≠ -x)
    (h₃ : 1 / (x + y) + z = 1) (h₄ : 1 / (y + z) + x = 1) (h₅ : 1 / (z + x) + y = 1) :
    (x, y, z) = (-1, -1, 3 / 2) ∨ (x, y, z) = (3 / 2, -1, -1) ∨ (x, y, z) = (-1, 3 / 2, -1) := by

  have h6 : x + y ≠ 0 := by
    intro h
    apply h₀
    linarith

  have h7 : y + z ≠ 0 := by
    intro h
    apply h₁
    linarith

  have h8 : z + x ≠ 0 := by
    intro h
    apply h₂
    linarith

  have eq1 : 1 = (x + y) * (1 - z) := by
    have h9 : x + y ≠ 0 := h6
    have h10 : 1 / (x + y) = 1 - z := by linarith
    field_simp at h10 ⊢
    nlinarith

  have eq2 : 1 = (y + z) * (1 - x) := by
    have h11 : y + z ≠ 0 := h7
    have h12 : 1 / (y + z) = 1 - x := by linarith
    field_simp at h12 ⊢
    nlinarith

  have eq3 : 1 = (z + x) * (1 - y) := by
    have h13 : z + x ≠ 0 := h8
    have h14 : 1 / (z + x) = 1 - y := by linarith
    field_simp at h14 ⊢
    nlinarith

  have eq4 : (x - z) * (1 + y) = 0 := by
    nlinarith

  have eq5 : (y - x) * (1 + z) = 0 := by
    nlinarith

  have eq6 : (z - y) * (1 + x) = 0 := by
    nlinarith

  cases (mul_eq_zero.mp eq4) with
  | inl h9 =>
    have h10 : x = z := by linarith
    have eq7 : (y - x) * (1 + z) = 0 := by
      nlinarith
    rw [show z = x by linarith [h10]] at eq7
    cases (mul_eq_zero.mp eq7) with
    | inl h11 =>
      have h12 : y = x := by linarith
      have eq8 : 1 = (x + x) * (1 - x) := by
        rw [show y = x by linarith [h12], show z = x by linarith [h10]] at eq1
        nlinarith
      have h15 : (2 * x ^ 2 - 2 * x + 1) = 0 := by
        nlinarith
      have h16 : (2 * x ^ 2 - 2 * x + 1) > 0 := by
        nlinarith [sq_nonneg (x - 1 / 2)]
      linarith
    | inr h11 =>
      have h17 : 1 + x = 0 := by
        nlinarith
      have h18 : x = -1 := by linarith
      have h19 : z = -1 := by
        linarith [h10, h18]
      have h20 : y = 3 / 2 := by
        rw [show x = -1 by linarith [h18], show z = -1 by linarith [h19]] at eq1
        nlinarith
      simp [h18, h20, h19]
  | inr h9 =>
    have h10 : y = -1 := by linarith
    have eq7 : 1 = (z + x) * (2) := by
      rw [show y = -1 by linarith [h10]] at eq3
      nlinarith
    have h11 : z + x = 1 / 2 := by
      nlinarith
    have h12 : 1 = (x + y) * (1 - z) := by
      nlinarith
    rw [show y = -1 by linarith [h10]] at h12
    have h13 : z = 1 / 2 - x := by linarith
    rw [show z = 1 / 2 - x by linarith [h13]] at h12
    have h14 : 2 * x ^ 2 - x - 3 = 0 := by
      nlinarith
    have h15 : (x - 3 / 2) * (2 * x + 2) = 0 := by
      nlinarith
    cases (mul_eq_zero.mp h15) with
    | inl h16 =>
      have h17 : x = 3 / 2 := by linarith
      have h18 : z = -1 := by
        linarith [h11, h17]
      simp [h17, h10, h18]
    | inr h16 =>
      have h17 : x = -1 := by linarith
      have h18 : z = 3 / 2 := by
        linarith [h11, h17]
      simp [h17, h10, h18]