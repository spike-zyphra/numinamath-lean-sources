import Mathlib

theorem algebra_1645 {a b p : ℝ} (h : ∀ x, (2 * x - 1)^2 - a * (x + b)^2 = p * x) :
    p = -8 ∨ p = 0 := by
  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3
  -- From $x = 0$ we get $1 - a \cdot b^2 = 0 \implies a \cdot b^2 = 1$
  have eq5 : a * b^2 = 1 := by
    nlinarith [eq1]
  -- From $x = 1$ we get $1 - a \cdot (1 + b)^2 = p \implies a \cdot (1 + b)^2 = 1 - p$
  have eq6 : a * (1 + b)^2 = 1 - p := by
    nlinarith [eq2, eq5]
  -- From $x = 2$ we get $9 - a \cdot (2 + b)^2 = 2p \implies a \cdot (2 + b)^2 = 9 - 2p$
  have eq7 : a * (2 + b)^2 = 9 - 2 * p := by
    nlinarith [eq3, eq5]
  -- From $x = 3$ we get $25 - a \cdot (3 + b)^2 = 3p \implies a \cdot (3 + b)^2 = 25 - 3p$
  have eq8 : a * (3 + b)^2 = 25 - 3 * p := by
    nlinarith [eq4, eq5]
  have h1 : a = 4 := by
    nlinarith [eq5, eq6, eq7]
  have h2 : b^2 = 1 / 4 := by
    nlinarith [eq5, h1]
  have h3 : b = 1 / 2 ∨ b = -1 / 2 := by
    have h4 : b^2 - (1 / 4) = 0 := by 
      linarith [h2]
    have h5 : (b - 1 / 2) * (b + 1 / 2) = 0 := by
      ring_nf at h4 ⊢
      linarith
    cases' (mul_eq_zero.mp h5) with h6 h7
    · left
      linarith
    · right
      linarith
  cases' h3 with hb1 hb2
  · -- Case b = 1/2
    have hp1 : p = -8 := by
      nlinarith [eq6, h1, hb1]
    left
    exact hp1
  · -- Case b = -1/2
    have hp2 : p = 0 := by
      nlinarith [eq6, h1, hb2]
    right
    exact hp2