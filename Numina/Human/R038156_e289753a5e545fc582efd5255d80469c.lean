import Mathlib

theorem algebra_7310 {n : ℕ} {F : Type*} [Field F] (A : Matrix (Fin n) (Fin n) F) :
    Nonempty (Invertible (A ^ 2)) ↔ Nonempty (Invertible (A ^ 3)) := by 
  have h1 : Nonempty (Invertible (A ^ 2)) ↔ Nonempty (Invertible A) := by
    apply Iff.intro
    · -- If A^2 is invertible, then A is invertible
      intro h
      simpa using h
    · -- If A is invertible, then A^2 is invertible
      intro h
      simpa using h
  have h2 : Nonempty (Invertible (A ^ 3)) ↔ Nonempty (Invertible A) := by
    apply Iff.intro
    · -- If A^3 is invertible, then A is invertible
      intro h
      simpa using h
    · -- If A is invertible, then A^3 is invertible
      intro h
      simpa using h
  rw [h1, h2]