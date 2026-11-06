import Mathlib

open Set

theorem number_theory_235743 :
    {n : ℤ | ∃ x y, n = x^2 + 2 * y^2} =
    {n : ℤ | ∃ x y, n = x^2 + 6 * x * y + 11 * y^2} := by
  ext n
  constructor
  · -- Assume n in left side, prove in right
    rintro ⟨x, y, h⟩
    use x - 3 * y
    use y
    nlinarith 
  · -- Assume n in right side, prove in left 
    rintro ⟨x, y, h⟩ 
    use x + 3 * y 
    use y 
    nlinarith