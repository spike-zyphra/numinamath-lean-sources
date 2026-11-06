import Mathlib

/-
Vind alle functies $f: \mathbb{R} \rightarrow \mathbb{R}$ waarvoor

$$
f\left(x^{2}\right)-f\left(y^{2}\right) \leq(f(x)+y)(x-f(y))
$$

voor alle $x, y \in \mathbb{R}$.
-/

theorem algebra_604199 (f : ℝ → ℝ) : (∀ x y : ℝ, f (x ^ 2) - f (y ^ 2) ≤ (f x + y) * (x - f y)) ↔ (f = fun x ↦ x) ∨ (f = fun x ↦ -x) := by
  constructor

  -- from left to right. We prove it by establishing several identities step by step, which all follow from the assumption easily.
  intro h
  have f00 : f 0 = 0 := by
    have tmp1 : f (0^2) - f (0^2) ≤ (f 0 + 0) * (0 - f 0) := by apply h 0 0
    field_simp at tmp1; exact real_inner_self_nonpos.mp tmp1
  have ft2 : ∀ t, f (t^2) = t * f t := by
    intro t
    have : - f (t^2) ≤ t * (- f t) := by
      have : f (0 ^ 2) - f (t ^ 2) ≤ (f 0 + t) * (0 - f t) := by apply h 0 t
      field_simp at this; ring_nf at this; rw [f00] at this; ring_nf at this;
      linarith
    have : f (t^2) ≤ (f t) * t := by
      have : f (t ^ 2) - f (0 ^ 2) ≤ (f t + 0) * (t - f 0) := by apply h t 0
      field_simp at this; ring_nf at this; rw [f00] at this; ring_nf at this;
      linarith
    linarith
  have fxfy : ∀ x y, f x  * f y ≤ x * y := by
    intro x y
    have fx2 : f (x^2) = x * f x := by apply ft2
    have fy2 : f (y^2) = y * f y := by apply ft2
    have tmp1 : f (x ^ 2) - f (y ^ 2) ≤ (f x + y) * (x - f y) := by apply h
    rw [fx2, fy2] at tmp1; ring_nf at tmp1; nlinarith

  -- the most important lemma : fx * f 1 = x.
  have fxf1 : ∀ x, f x * f 1 = x := by
    intro x
    have : (f x)*(f 1) ≤ x * 1 := by apply fxfy
    have : - (f x)*(f (-1)) = (f x) * (f 1) := by
      have : f 1 = - f (-1) := by
        have : f ((-1)^2) = (-1) * f (-1) := by apply ft2
        field_simp at this; assumption
      rw [this]; ring
    have : -x * (-1) ≤ - (f x) * (f (-1)) := by
      have : f x * f (-1) ≤ x * (-1) := by apply fxfy
      linarith
    nlinarith

  -- by the previous lemma, we have (f 1)^2 = 1, so there are two cases, corresponding to f x = x and f x = -x.
  have f12 : (f 1)^2 = 1 := by
    have : f 1 * f 1 = 1 := by apply fxf1
    rw [pow_two]; assumption
  have f1eq1orf1eqm1 : f 1 = 1 ∨ f 1 = -1 := by exact mul_self_eq_one_iff.mp (fxf1 1)

  obtain f1eq1 | f1eqm1 := f1eq1orf1eqm1

  left
  have fxeqx : ∀ x, f x = x := by
    intro x
    rw [f1eq1] at fxf1; simp at fxf1; simp [fxf1]
  ext x; apply fxeqx x

  right
  have fxeqmx : ∀ x, f x = - x:= by
    intro x
    rw [f1eqm1] at fxf1; simp at f1eqm1;
    have : f x * -1 = x := by apply fxf1
    linarith
  ext x; apply fxeqmx x


  -- from right to left. A simple calculation.
  intro h
  obtain allxfxeqx | allxfxeqmx := h

  intro x y
  simp [allxfxeqx]; ring_nf; linarith

  intro x y
  simp [allxfxeqmx]; ring_nf; linarith
