import Mathlib

theorem number_theory_230834 {a b : ℤ} (ha : ∃ x y z w : ℤ, a = x^2 + y^2 + z^2 + w^2)
    (hb : ∃ x y z w : ℤ, b = x^2 + y^2 + z^2 + w^2) :
    ∃ x y z w : ℤ, a * b = x^2 + y^2 + z^2 + w^2 := by
  rcases ha with ⟨a1, a2, a3, a4, ha⟩
  rcases hb with ⟨b1, b2, b3, b4, hb⟩
  use a1 * b1 - a2 * b2 - a3 * b3 - a4 * b4
  use a1 * b2 + a2 * b1 + a3 * b4 - a4 * b3
  use a1 * b3 - a2 * b4 + a3 * b1 + a4 * b2
  use a1 * b4 + a2 * b3 - a3 * b2 + a4 * b1
  rw [ha, hb]
  ring_nf