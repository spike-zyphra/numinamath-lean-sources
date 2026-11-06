import Mathlib

  theorem number_theory_107515 :
  {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ 9 * (x ^ 2 + y ^ 2 + 1) + 2 * (3 * x * y + 2) = 2005} = {(11, 7), (7, 11)} := by
  ext ⟨x, y⟩
  simp
  constructor
  · -- First prove the original equation implies the solutions
    rintro ⟨hx, hy, heq⟩
    have h1 : x ≤ 32 := by
      nlinarith
    have h2 : y ≤ 32 := by
      nlinarith
    interval_cases x <;> interval_cases y
    <;> norm_num at heq hx hy
    <;> tauto
  · -- Now prove the solutions satisfy the equation
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- Check (11, 7)
      constructor
      · norm_num -- x > 0
      constructor
      · norm_num -- y > 0
      · norm_num -- the equation
    · -- Check (7, 11)
      constructor
      · norm_num -- x > 0
      constructor
      · norm_num -- y > 0
      · norm_num -- the equation