import Mathlib

theorem number_theory_263044 (u : ℤ) :
    (∃ m n l : ℤ, u = 12 * m + 8 * n + 4 * l) ↔
    (∃ p q r : ℤ, u = 20 * p + 16 * q + 12 * r) := by
  constructor
  · -- Assume exists m n l : ℤ, u = 12 * m + 8 * n + 4 * l prove exists p q r : ℤ, u = 20 * p + 16 * q + 12 * r
    rintro ⟨m, n, l, h⟩
    have h1 : u = 4 * (3 * m + 2 * n + l) := by linarith
    refine ⟨-2 * (3 * m + 2 * n + l), 2 * (3 * m + 2 * n + l), (3 * m + 2 * n + l), by linarith⟩
  · -- Assume exists p q r : ℤ, u = 20 * p + 16 * q + 12 * r prove exists m n l : ℤ, u = 12 * m + 8 * n + 4 * l
    rintro ⟨p, q, r, h⟩
    have h1 : u = 4 * (5 * p + 4 * q + 3 * r) := by linarith
    refine ⟨5 * p + 4 * q + 3 * r, -(5 * p + 4 * q + 3 * r), 0, by linarith⟩