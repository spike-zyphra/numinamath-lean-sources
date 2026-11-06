import Mathlib

theorem algebra_6536
    {a : ℝ}
    (ha : 0 < a ∧ a ≠ -1)
    (h : a / 2 + 1 / (a + 1) = 11 * a / 4) :
    a = 1 / 3 := by
  have h1 : a + 1 ≠ 0 := by
    intro h_zero
    apply ha.right
    linarith
  have h2 : 0 < a := ha.1
  have eq1 : a / 2 + 1 / (a + 1) = 11 * a / 4 := h
  have h3 : (a + 1) ≠ 0 := h1
  have eq2 : (a / 2 + 1 / (a + 1)) * (a + 1) = (11 * a / 4) * (a + 1) := by
    rw [eq1]
  have eq3 : (a / 2 + 1 / (a + 1)) * (a + 1) = (a / 2) * (a + 1) + 1 := by
    field_simp [h3]
    <;> ring_nf
  have eq4 : (a / 2) * (a + 1) + 1 = (11 * a / 4) * (a + 1) := by
    linarith [eq2, eq3]
  have eq5 : 9 * a ^ 2 + 9 * a - 4 = 0 := by
    nlinarith [eq4, h2]
  have h_eq5 : (a - 1 / 3) * (9 * a + 15) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h_eq5) with h_eq6 h_eq7
  · -- Case where $a - 1/3 = 0$
    linarith
  · -- Case where $9a + 15 = 0$
    linarith [h2, show a = -5 / 3 by linarith]