import Mathlib

theorem algebra_95428_1 (a b c d e f : ℤ) (h₀ : a + b = 26) (h₁ : a + b + c + d = 41)
    (h₂ : a + b + c + d + e + f = 57) :
    Even a ∨ Even b ∨ Even c ∨ Even d ∨ Even e ∨ Even f := by
  -- One has to be even:
  by_contra h
  -- if all were odd,
  push_neg at h
  -- we could choose a', b', ... such that 2a' + 1 + 2b' + 1 + 2c' + 1 + 2d' + 1 = 41.
  rw[Int.not_even_iff_odd, Int.not_even_iff_odd, Int.not_even_iff_odd, Int.not_even_iff_odd,
     Int.not_even_iff_odd, Int.not_even_iff_odd] at h
  obtain ⟨⟨ka,rfl⟩, ⟨kb,rfl⟩, ⟨kc,rfl⟩, ⟨kd,rfl⟩, ⟨ke,rfl⟩, ⟨kf,rfl⟩⟩ := h
  -- But 2a' + 1 + 2b' + 1 + 2c' + 1 + 2d' + 1 = 2 (a' + b' + c' + d' + 2), hence it is even,
  have : Even (2 * ka + 1 + (2 * kb + 1) + (2 * kc + 1) + (2 * kd + 1)) := by
    exists ka + kb + kc + kd + 2
    ring
  -- unlike 41. Contradiction.
  rw[h₁] at this
  contradiction

theorem algebra_95428_2 : ∃ a b c d e f : ℤ, a + b = 26 ∧ a + b + c + d = 41 ∧
    a + b + c + d + e + f = 57 ∧ Odd a ∧ Odd b ∧ Even c ∧ Odd d ∧ Odd e ∧ Odd f := by

  use 13, 13, 8, 7, 9, 7
  constructor
  · norm_num -- a + b = 26
  constructor
  · norm_num -- a + b + c + d = 41
  constructor
  · norm_num -- a + b + c + d + e + f = 57
  constructor
  · decide -- Odd a
  constructor
  · decide -- Odd b
  constructor
  · decide -- Even c
  constructor
  · decide -- Odd d
  constructor
  · decide -- Odd e
  · decide -- Odd f