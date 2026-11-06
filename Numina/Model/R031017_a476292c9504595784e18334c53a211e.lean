import Mathlib

theorem number_theory_19184 :
    IsEmpty {x : ℤ | 0 ≤ x ∧ x < 12 ∧
    x - 1 ≡ 1 - x [ZMOD 12] ∧
    x - 2 ≡ 2 - x [ZMOD 12]} := by 
  have h1 : {x : ℤ | 0 ≤ x ∧ x < 12 ∧
      x - 1 ≡ 1 - x [ZMOD 12] ∧
      x - 2 ≡ 2 - x [ZMOD 12]} = ∅ := by
    ext x
    simp [Int.ModEq]
    <;> omega
  rw [h1]
  simp