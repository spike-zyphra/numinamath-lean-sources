import Mathlib.Data.Int.Defs
import Mathlib.Tactic.Use
import Mathlib.Tactic.Ring

theorem number_theory_221928 {a b : ℤ} (ha : ∃ x y z w, a = x^2 + y^2 + z^2 + w^2)
    (hb : ∃ u v w x, b = u^2 + v^2 + w^2 + x^2) :
    ∃ y z w u, a * b = y^2 + z^2 + w^2 + u^2 := by
  rcases ha with ⟨p, q, r, s, ha⟩
  rcases hb with ⟨p', q', r', s', hb⟩
  use p * p' + q * q' + r * r' + s * s'
  use p * q' - q * p' + r * s' - s * r'
  use p * r' - r * p' + s * q' - q * s'
  use p * s' - s * p' + q * r' - r * q'
  rw [ha, hb]
  ring_nf