import Mathlib

theorem algebra_2524 {P Q R : ℝ}
    (hP : P = -1 / (12345 * 12346 : ℝ))
    (hQ : Q = -1 / (12344 * 12346 : ℝ))
    (hR : R = -1 / (12344 * 12345 : ℝ)) :
    P > Q ∧ Q > R := by
  rw [hP, hQ, hR]
  constructor
  · -- Show that $P > Q$
    norm_num
  · -- Show that $Q > R$
    norm_num