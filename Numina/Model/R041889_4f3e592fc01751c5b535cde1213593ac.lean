import Mathlib

open Real

theorem algebra_10351 {f : ℝ → ℝ} (hf : f = fun x => 3 * x - 8) : {x | f x = Function.invFun f x} = {4} := by
  have h1 : ∀ x, f x = 3 * x - 8 := by
    intro x
    rw [hf]
  have h2 : ∀ x, Function.invFun f x = (x + 8) / 3 := by
    intro x
    have h_inv : ∀y : ℝ, f y = x ↔ y = (x + 8) / 3 := by
      intro y
      constructor
      · -- Assume f(y) = x
        intro h_eq
        rw [h1 y] at h_eq
        linarith
      · -- Assume y = (x + 8) / 3
        intro h_eq
        rw [h_eq]
        rw [h1]
        ring_nf
    rw [Function.invFun]
    simp_all [h_inv]
  ext x
  simp [h1, h2]
  constructor
  · -- First direction: if f(x) = f⁻¹(x), then x = 4.
    intro h_eq
    linarith
  · -- Second direction: if x = 4, then f(x) = f⁻¹(x).
    intro h_eq
    rw [h_eq]
    norm_num