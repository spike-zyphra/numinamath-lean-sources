import Mathlib

theorem algebra_132079 {x y : ℝ} (hxy : x ≠ y) (h1 : x + 1 / (y - x) = 1) (h2 : y + 1 / (x - y) = 2) :
    (x = 2 ∧ y = 1) ∨ (x = 1 / 2 ∧ y = 5 / 2) := by

  have hne1 : y - x ≠ 0 := by
    intro h
    apply hxy
    linarith

  have hne2 : x - y ≠ 0 := by
    intro h
    apply hxy
    linarith

  have eq1 : x * (y - x) + 1 = y - x := by
    have h : x + 1 / (y - x) = 1 := h1
    field_simp [hne1] at h ⊢
    linarith

  have eq2 : y * (x - y) + 1 = 2 * (x - y) := by
    have h : y + 1 / (x - y) = 2 := h2
    field_simp [hne2] at h ⊢
    linarith

  have eq3 : (x - 1) * (y - x) = -1 := by
    nlinarith

  have eq4 : (y - 2) * (x - y) = -1 := by
    nlinarith

  have eq5 : (x - 1) * (x - y) = 1 := by
    have eq_u : (x - 1) * (y - x) = -1 := eq3
    have eq_eq : (x - 1) * (x - y) = 1 := by
      have : (x - 1) * (x - y) = -( (x - 1) * (y - x) ) := by
        ring_nf
      rw [this]
      linarith [eq_u]
    linarith

  have eq7 : (x - y) ^ 2 + (x - y) - 2 = 0 := by
    nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_pos_of_ne_zero (sub_ne_zero.2 hxy)] 

  have h_eq : ((x - y) + 2) * ((x - y) - 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.1 h_eq) with h_eq1 h_eq2

  · -- Case $ (x - y) + 2 = 0 \implies x - y = -2 $.
    have h_eq1' : x - y = -2 := by linarith

    have hx : x = 1 / 2 := by
      nlinarith

    have hy : y = 5 / 2 := by
      nlinarith

    right
    constructor
    · linarith
    · linarith

  · -- Case $ (x - y) - 1 = 0 \implies x - y = 1 $.
    have h_eq2' : x - y = 1 := by linarith

    have hx : x = 2 := by
      nlinarith

    have hy : y = 1 := by
      nlinarith

    left
    constructor
    · linarith
    · linarith