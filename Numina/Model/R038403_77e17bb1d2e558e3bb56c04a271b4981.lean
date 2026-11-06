import Mathlib

theorem algebra_223990 {a : Fin 3 → Fin 3 → ℝ} {b c : Fin 3 → ℝ}
    (h : ∀ x y z, a 0 0 * x ^ 2 + a 1 1 * y ^ 2 + a 2 2 * z ^ 2 +
      2 * a 0 1 * x * y + 2 * a 0 2 * x * z + 2 * a 1 2 * y * z =
      (b 0 * x + b 1 * y + b 2 * z) * (c 0 * x + c 1 * y + c 2 * z)) :
    a 0 0 * a 1 1 * a 2 2 + 2 * a 0 2 * a 0 1 * a 1 2 =
    a 1 2 ^ 2 * a 0 0 + a 0 2 ^ 2 * a 1 1 + a 0 1 ^ 2 * a 2 2 := by
  have eq1 := h 1 0 0
  have eq2 := h 0 1 0 
  have eq3 := h 0 0 1
  have eq4 := h 1 1 0
  have eq5 := h 1 0 1
  have eq6 := h 0 1 1
  have eq7 := h 1 1 1
  simp [Fin.sum_univ_three] at eq1 eq2 eq3 eq4 eq5 eq6 eq7
  have eq8 : a 0 0 = b 0 * c 0 := by
    linarith
  have eq9 : a 1 1 = b 1 * c 1 := by
    nlinarith
  have eq10 : a 2 2 = b 2 * c 2 := by
    nlinarith
  have eq11 : 2 * a 0 1 = b 0 * c 1 + b 1 * c 0 := by
    nlinarith
  have eq12 : 2 * a 0 2 = b 0 * c 2 + b 2 * c 0 := by
    nlinarith
  have eq13 : 2 * a 1 2 = b 1 * c 2 + b 2 * c 1 := by
    nlinarith
  have eq14 : a 0 1 = (b 0 * c 1 + b 1 * c 0) / 2 := by
    linarith
  have eq15 : a 0 2 = (b 0 * c 2 + b 2 * c 0) / 2 := by
    linarith
  have eq16 : a 1 2 = (b 1 * c 2 + b 2 * c 1) / 2 := by
    linarith
  rw [eq8, eq9, eq10, eq14, eq15, eq16]
  ring_nf