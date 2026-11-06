import Mathlib

/-- Two integers have a sum of 26. When two more integers are added to the first two, the sum is 41.
  Finally, when two more integers are added to the sum of the previous 44 integers, the sum is 57.
  What is the minimum number of even integers among the 6 integers?
(A) 1(B) 2(C) 3(D) 4(E) 5 -/
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

/-- Two integers have a sum of 26. When two more integers are added to the first two, the sum is 41.
  Finally, when two more integers are added to the sum of the previous 44 integers, the sum is 57.
  What is the minimum number of even integers among the 6 integers?
(A) 1(B) 2(C) 3(D) 4(E) 5 -/
theorem algebra_95428_2 : ∃ a b c d e f : ℤ, a + b = 26 ∧ a + b + c + d = 41 ∧
    a + b + c + d + e + f = 57 ∧ Odd a ∧ Odd b ∧ Even c ∧ Odd d ∧ Odd e ∧ Odd f := by
  -- One even number is sufficient though:
  -- Choose a = 1,
  use 1
  -- b = 25,
  use 25
  -- c = 14,
  use 14
  -- d = 1,
  use 1
  -- e = 1,
  use 1
  -- f = 15,
  use 15
  -- then only c is even and all the equations hold.
  decide