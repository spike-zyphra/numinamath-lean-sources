import Mathlib

theorem algebra_150 (a b c d : ℝ) (ha : a ≠ b) (hb : a ≠ c) (hc : a ≠ d)
(hd : b ≠ c) (he : b ≠ d) (hf : c ≠ d)
(hroots : {x | x^2 - 10 * c * x - 11 * d = 0} = {a, b})
(hroots' : {x | x^2 - 10 * a * x - 11 * b = 0} = {c, d}) :
a + b + c + d = 1210 := by

  have h1 : a ^ 2 - 10 * c * a - 11 * d = 0 := by
    have h2 : a ∈ {x | x^2 - 10 * c * x - 11 * d = 0} := by
      rw [show {x | x^2 - 10 * c * x - 11 * d = 0} = {a, b} by rw [hroots]]
      simp
    simpa using h2

  have h2 : b ^ 2 - 10 * c * b - 11 * d = 0 := by
    have h3 : b ∈ {x | x^2 - 10 * c * x - 11 * d = 0} := by
      rw [show {x | x^2 - 10 * c * x - 11 * d = 0} = {a, b} by rw [hroots]]
      simp
    simpa using h3

  have h3 : c ^ 2 - 10 * a * c - 11 * b = 0 := by
    have h4 : c ∈ {x | x^2 - 10 * a * x - 11 * b = 0} := by
      rw [show {x | x^2 - 10 * a * x - 11 * b = 0} = {c, d} by rw [hroots']]
      simp
    simpa using h4

  have h4 : d ^ 2 - 10 * a * d - 11 * b = 0 := by
    have h5 : d ∈ {x | x^2 - 10 * a * x - 11 * b = 0} := by
      rw [show {x | x^2 - 10 * a * x - 11 * b = 0} = {c, d} by rw [hroots']]
      simp
    simpa using h5

  have h5 : a + b = 10 * c := by
    have eq1 : a ^ 2 - 10 * c * a - 11 * d = 0 := h1
    have eq2 : b ^ 2 - 10 * c * b - 11 * d = 0 := h2
    have eq3 : (a - b) * (a + b - 10 * c) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq3) with h6 h7
    · -- a - b = 0, so a = b
      exfalso
      apply ha
      linarith
    · -- a + b - 10 * c = 0
      linarith

  have h6 : c + d = 10 * a := by
    have eq1 : c ^ 2 - 10 * a * c - 11 * b = 0 := h3
    have eq2 : d ^ 2 - 10 * a * d - 11 * b = 0 := h4
    have eq3 : (c - d) * (c + d - 10 * a) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp eq3) with h7 h8
    · -- c - d = 0, so c = d
      exfalso
      apply hf
      linarith
    · -- c + d - 10 * a = 0
      linarith

  -- Solving the system of equations
  have eq3 : b = 10 * c - a := by linarith
  have eq4 : d = 10 * a - c := by linarith

  rw [eq3] at h2 h3
  rw [eq4] at h1 h4

  nlinarith [sq_pos_of_ne_zero (show a - b ≠ 0 by
    intro h
    apply ha
    linarith
  ), sq_pos_of_ne_zero (show a - c ≠ 0 by
    intro h
    apply hb
    linarith
  ), sq_pos_of_ne_zero (show a - d ≠ 0 by
    intro h
    apply hc
    linarith
  ), sq_pos_of_ne_zero (show b - c ≠ 0 by
    intro h
    apply hd
    linarith
  ), sq_pos_of_ne_zero (show b - d ≠ 0 by
    intro h
    apply he
    linarith
  ), sq_pos_of_ne_zero (show c - d ≠ 0 by
    intro h
    apply hf
    linarith
  )]