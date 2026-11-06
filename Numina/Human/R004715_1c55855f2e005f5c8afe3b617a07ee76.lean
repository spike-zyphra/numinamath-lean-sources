import Mathlib

open Set

/- x.toNat = n ↔ x = n if n is a positive integer -/
lemma int_cast_eq_iff {n : ℕ} (hn : 0 < n) (x : ℤ) :
    x.toNat = n ↔ x = n := by
  -- x ≤ 0 ∨ 0 ≤ x
  rcases le_total x 0 with hx | hx
  . rw [Int.toNat_of_nonpos hx]
    omega
  . zify
    rw [Int.toNat_of_nonneg hx]

/-  -/
theorem inequalites_308627 :
    {a : ℝ | {x : ℤ | 0 < x ∧ 3 * (x - 1) < 2 * (x + a) - 5}.encard = 3} = Ioc (5 / 2) 3 := by
  -- We first show that the set is the the set of integers in the interval (0, 2a - 2)
  have H {a : ℝ} : {x : ℤ | 0 < x ∧ 3 * (x - 1) < 2 * (x + a) - 5} = Int.cast ⁻¹' (Ioo 0 (2 * a - 2)) := by
    ext x
    -- Simplify the expression
    simp [-Int.preimage_Ioo]
    rintro -
    -- We show `3 * (↑x - 1) < 2 * (↑x + a) - 5` iff `↑x < 2 * a - 2`
    constructor
    all_goals
      intro h
      linarith
  -- So the solution set has ↑(⌈2 * a⌉ - 2) - 1 elements
  simp [H, ← Finset.coe_Ioo]
  ext a
  norm_cast
  simp
  -- We show the equivalence of the two expressions
  calc (⌈2 * a⌉ - 2).toNat = 4
    _ ↔ ⌈2 * a⌉ - 2 = 4 := int_cast_eq_iff (show 0 < 4 by simp) _
    _ ↔ ⌈2 * a⌉ = 6 := eq_iff_eq_of_sub_eq_sub (by ring)
    _ ↔ 6 - 1 < 2 * a ∧ 2 * a ≤ 6 := Int.ceil_eq_iff
    _ ↔ 5 / 2 < a ∧ a ≤ 3 := by constructor <;> (intro ⟨h₁, h₂⟩; constructor <;> linarith)
