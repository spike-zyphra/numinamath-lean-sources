import Mathlib

theorem algebra_11476 {x y : ℝ} (h : x + y = 1) :
    (x^3 + 1) * (y^3 + 1) ≤ (1 ^ 3 + 1) * (1 ^ 3 + 1) ∧
    (x * y = -1 ↔ (x^3 + 1) * (y^3 + 1) = (1 ^ 3 + 1) * (1 ^ 3 + 1)) := by
  constructor
  · -- Show inequality
    have eq1 : (1 ^ 3 + 1 : ℝ) * (1 ^ 3 + 1) = (4 : ℝ) := by norm_num
    rw [eq1]
    have eq2 : (x^3 + 1) * (y^3 + 1) = (x * y)^3 + (x^3 + y^3) + 1 := by
      ring_nf
    have eq3 : x^3 + y^3 = 1 - 3 * (x * y) := by
      have eq4 : x + y = 1 := h
      calc
        x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by ring
        _ = 1 ^ 3 - 3 * (x * y) * 1 := by rw [eq4]
        _ = 1 - 3 * (x * y) := by ring
    rw [eq2, eq3]
    have h_eq : x * y ≤ 1 / 4 := by
      have h1 : y = 1 - x := by linarith
      rw [show y = 1 - x by linarith [h]]
      nlinarith [sq_nonneg (x - 1 / 2)]
    nlinarith [sq_nonneg (x * y + 1), sq_nonneg ((x * y) * y), sq_nonneg ((x + y) * (x * y) ), sq_nonneg ((x - y)  ^ 2), h_eq, sq_nonneg (x -1/2), sq_nonneg (y -1/2) ]
  constructor
  · -- Show that if $x * y = -1$, then $(x^3 + 1) * (y^3 + 1) = 4$.
    intro h_eq
    have h_eq1 : x * y = -1 := h_eq
    have h_eq2 : x ^ 3 + y ^ 3 = 4 := by
      have eq1 : x + y = 1 := h
      have eq2 : x * y = -1 := h_eq1
      have eq3 : x ^ 3 + y ^ 3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
        ring_nf
      rw [eq1, eq2] at eq3
      linarith [eq3]
    have h_eq3 : (x^3 + 1) * (y^3 + 1) = 4 := by
      calc
        (x^3 + 1) * (y^3 + 1) = x^3 * y^3 + x^3 + y^3 + 1 := by ring
        _ = (x * y) ^ 3 + x^3 + y^3 + 1 := by ring
        _ = (-1) ^ 3 + x^3 + y^3 + 1 := by rw [show x * y = -1 by linarith [h_eq1]]
        _ = -1 + x^3 + y^3 + 1 := by norm_num
        _ = x^3 + y^3 := by ring
        _ = 4 := by linarith [h_eq2]
    linarith [h_eq3]
  · -- Show that if $(x^3 + 1) * (y^3 + 1) = 4$, then $x * y = -1$.
    intro h_eq
    have h_eq1 : (x^3 + 1) * (y^3 + 1) = 4 := by
      linarith [h_eq, show (1 ^ 3 + 1 : ℝ) * (1 ^ 3 + 1) = 4 by norm_num]
    have h_eq2 : x * y = -1 := by
      have h_eq3 : (x * y) ^ 3 - 3 * (x * y) - 2 = 0 := by
        have h1 : (x^3 + 1) * (y^3 + 1) = (x * y) ^ 3 + (x^3 + y^3) + 1 := by
          ring_nf
        have h2 : x^3 + y^3 = 1 - 3 * (x * y) := by
          have eq1 : x + y = 1 := h
          have eq3 : x^3 + y^3 = (x + y) ^ 3 - 3 * (x * y) * (x + y) := by
            ring_nf
          rw [eq1] at eq3
          linarith [eq3]
        rw [h1, h2] at h_eq1
        nlinarith [h_eq1]
      have h_eq4 : (x * y + 1) ^ 2 * (x * y - 2) = 0 := by
        nlinarith [h_eq3]
      cases' (mul_eq_zero.mp h_eq4) with h_eq5 h_eq6
      · -- First case: $(x*y+1)^2 = 0$, so $xy = -1$.
        have : x * y + 1 = 0 := by
          have : (x * y + 1) ^ 2 = 0 := by nlinarith [h_eq5]
          nlinarith
        linarith
      · -- Second case: $x*y - 2 = 0$, so $xy = 2$. But this is impossible given $x+y = 1$.
        nlinarith [sq_nonneg (x - y), sq_nonneg (x -1/2), sq_nonneg (y -1/2),
          h]
    assumption