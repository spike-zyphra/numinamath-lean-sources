import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_297276 : {a : ℝ | ∃ x : ℝ, cos (2 * x) + sin x = a} = {a | -2 ≤ a ∧ a ≤ 9 / 8} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_setOf_eq]
  constructor
  · -- First, show that if a is in the left-hand side, it is in the right-hand side
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
      have h2 : cos (2 * x) = 1 - 2 * sin x ^ 2 := by
        rw [cos_two_mul, sin_sq]
        <;> ring
      linarith
    have h2 : a = 1 - 2 * sin x ^ 2 + sin x := by
      linarith [hx, h1]
    have h3 : -1 ≤ sin x ∧ sin x ≤ 1 := sin_mem_Icc x
    have h4 : -1 ≤ sin x := h3.1
    have h5 : sin x ≤ 1 := h3.2
    constructor
    · -- Show that -2 ≤ a
      nlinarith [sq_nonneg (sin x + 1), sq_nonneg (sin x - 1 / 4)]
    · -- Show that a ≤ 9/8
      nlinarith [sq_nonneg (sin x - 1 / 4), sq_nonneg (sin x - 1), sq_nonneg (sin x + 1)]
  · -- Now the reverse direction: if $a \in \[-2, 9/8\]$, there is a solution.
    intro h
    rcases h with ⟨ha1, ha2⟩
    have h6 : ∃ y, -1 ≤ y ∧ y ≤ 1 ∧ (1 - 2 * y ^ 2 + y = a) := by
      use (1 - Real.sqrt (9 - 8 * a)) / 4
      constructor
      · -- Show that -1 ≤ (1 - Real.sqrt (9 - 8 * a)) / 4
        nlinarith [Real.sqrt_nonneg (9 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * a by nlinarith)]
      constructor
      · -- Show that (1 - Real.sqrt (9 - 8 * a)) / 4 ≤ 1
        nlinarith [Real.sqrt_nonneg (9 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * a by nlinarith)]
      · -- Show that 1 - 2 * ((1 - Real.sqrt (9 - 8 * a)) / 4) ^ 2 + (1 - Real.sqrt (9 - 8 * a)) / 4 = a
        nlinarith [Real.sqrt_nonneg (9 - 8 * a), Real.sq_sqrt (show (0 : ℝ) ≤ 9 - 8 * a by nlinarith)]
    rcases h6 with ⟨y, hy1, hy2, heq⟩
    use Real.arcsin y
    have h10 : sin (Real.arcsin y) = y := by
      apply sin_arcsin
      linarith
      linarith
    have h11 : cos (2 * (Real.arcsin y)) = 1 - 2 * sin (Real.arcsin y) ^ 2 := by
      rw [cos_two_mul, sin_sq]
      <;> ring
    rw [h11, h10]
    linarith [heq]