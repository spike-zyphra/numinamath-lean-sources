import Mathlib

theorem algebra_237166 (a : Fin 2014 → Fin 2014 → ℤ)
    (ha : ∀ i j, a i j = (-1) ^ (i.1 + 1) * (2015 - (i.1 + 1) - (j.1 + 1)) ^ 2) :
    ∑ i, ∑ j, a i j = 0 := by
  have h1 : ∀ i j, a i j = (-1) ^ (i.1 + 1) * (2015 - (i.1 + 1) - (j.1 + 1)) ^ 2 := ha
  simp_all [ha]
  <;> native_decide
  <;> try { native_decide }