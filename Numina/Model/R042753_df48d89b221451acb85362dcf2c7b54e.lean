import Mathlib

open MvPolynomial

theorem algebra_290995 {R : Type*} [CommRing R] :
  let x : MvPolynomial (Fin 2) R := X ⟨0, by decide⟩
  let y : MvPolynomial (Fin 2) R := X ⟨1, by decide⟩
  (x^7 + x^6 * y + x^5 * y^2 + x^4 * y^3 + x^3 * y^4 + x^2 * y^5 + x * y^6 + y^7) =
  (x + y) * (x^2 + y^2) * (x^4 + y^4) := by

  intro x y
  ring