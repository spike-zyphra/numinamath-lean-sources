import Mathlib

theorem algebra_7310 {n : ℕ} {F : Type*} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    Nonempty (Invertible (A ^ 2)) ↔ Nonempty (Invertible (A ^ 3)) := by
  constructor
  · -- Assume Nonempty (Invertible (A ^ 2)), prove Nonempty (Invertible (A ^ 3))
    intro h
    simpa using h
  · -- Assume Nonempty (Invertible (A ^ 3)), prove Nonempty (Invertible (A ^ 2))
    intro h
    simpa using h