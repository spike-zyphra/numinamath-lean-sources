import Mathlib

open MvPolynomial

theorem algebra_286934 {R : Type*} [CommRing R] :
  let a : MvPolynomial (Fin 3) R := X ⟨0, by decide⟩
  let b : MvPolynomial (Fin 3) R := X ⟨1, by decide⟩
  let c : MvPolynomial (Fin 3) R := X ⟨2, by decide⟩

  a * (b - c) ^ 3 + b * (c - a) ^ 3 + c * (a - b) ^ 3 = (a - b) * (b - c) * (c - a) * (a + b + c) := by
  intro a b c
  ring