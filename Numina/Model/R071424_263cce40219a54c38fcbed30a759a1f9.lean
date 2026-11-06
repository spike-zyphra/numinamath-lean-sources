import Mathlib

/- Let the function $f$: ${1,2,3} \to {2,3,4}$ satisfy $f[f(x)-1]=f(x)$, then the number of such functions is ___          ___. -/
theorem algebra_8398 :
    Set.ncard {f : Fin 3 → Fin 3 | ∀ x, f (f x - 1) = f x} = 10 := by
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card]
  <;> native_decide