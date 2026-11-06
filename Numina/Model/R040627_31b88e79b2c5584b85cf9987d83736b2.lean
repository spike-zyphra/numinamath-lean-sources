import Mathlib

theorem algebra_173765 {a : ℝ} (ha : a ≠ 0 ∧ a ≠ 2 ∧ a ≠ -2) :
    (a^2 + 2 * a + 4 + 8 / a + 16 / a^2 + 64 / ((a - 2) * a^2)) *
    (a^2 - 2 * a + 4 - 8 / a + 16 / a^2 - 64 / ((a + 2) * a^2)) =
    (a^2 + 2 * a + 4 + 8 / a + 16 / a^2) * (a^2 - 2 * a + 4 - 8 / a + 16 / a^2) := by
  rcases ha with ⟨ha1, ha2, ha3⟩
  field_simp [(show a - 2 ≠ 0 by
    intro h 
    apply ha2
    linarith
  ), (show a + 2 ≠ 0 by 
    intro h 
    apply ha3 
    linarith
  ), ha1, show a^2 ≠ 0 by
    have : a ≠ 0 := ha1
    simp [this]
  ]
  <;> ring