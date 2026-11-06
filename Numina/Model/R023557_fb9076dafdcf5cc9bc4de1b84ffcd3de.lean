import Mathlib

theorem calculus_16644 (a : ℝ) (ha : a ≠ 0) :
    Matrix.det (fun i j : Fin 3 => if i = j then x + a else x) = 0 ↔ x = -a / 3 := by
  simp [Matrix.det_fin_three, Fin.sum_univ_three, mul_add, add_mul]
  constructor
  · -- Forward direction: determinant = 0 ⇒ x = -a/3
    intro h
    have h1 : 3 * a^2 * x + a^3 = 0 := by
      nlinarith
    have h2 : a * (3 * a * x + a^2) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.mp h2) with ha1 ha2
    · -- Contradiction since a ≠ 0
      exfalso
      exact ha (by simpa using ha1)
    · -- Solving 3 * a * x + a^2 = 0
      have h3 : 3 * a * x + a^2 = 0 := by
        linarith
      have h4 : 3 * a * x = -a^2 := by
        linarith
      have h5 : x = -a / 3 := by
        have h2 : a ≠ 0 := by simpa using ha
        apply (mul_right_inj' (show 3 * a ≠ 0 by
          intro h
          have h1 : a = 0 := by
            nlinarith [h]
          contradiction
        )).mp
        linarith
      linarith
  · -- Backward direction: x = -a/3 ⇒ determinant = 0
    intro h
    rw [h]
    ring