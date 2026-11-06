import Mathlib

open Set

theorem inequalities_603985 :
    {x : ℝ | 0 ≤ 3 - x ∧ 0 ≤ x + 1 ∧ √(3 - x) - √(x + 1) > 1 / 2} = Ico (-1) (1 - √31 / 8) := by
  set f := fun x ↦ √(3 - x) - √(x + 1) with hf
  have h₁ : StrictAntiOn f (Icc (-1) 3) := by
    intro x ⟨hx₁, hx₂⟩ y ⟨hy₁, hy₂⟩ h
    simp [hf]
    suffices √(3 - y) < √(3 - x) ∧ √(x + 1) < √(y + 1) by linarith
    constructor
    all_goals
      rw [Real.sqrt_lt_sqrt_iff (by linarith)]
      linarith
  have h₂ : f (1 - √31 / 8) = 1 / 2 := by
    simp [hf]
    ring_nf
    have k₁ : 2 + √31 * (1 / 8) = ((√31 + 1) / 4) ^ 2 := by
      ring_nf
      norm_num
      ring
    have k₁' : 0 ≤ (√31 + 1) / 4 := by positivity
    have k₂ : 2 + √31 * (-1 / 8) = ((√31 - 1) / 4) ^ 2 := by
      ring_nf
      norm_num
      ring
    have k₂' : 0 ≤ (√31 - 1) / 4 := by
      suffices 1 ≤ √31 by linarith
      exact Real.one_le_sqrt.mpr (by simp)
    rw [k₁, k₂]
    simp [k₁', k₂']
    ring
  have H (x : ℝ) : 0 ≤ 3 - x ∧ 0 ≤ x + 1 → (√(3 - x) - √(x + 1) > 1 / 2 ↔ x < 1 - √31 / 8) := by
    intro ⟨hx₁, hx₂⟩
    rw [show √(3 - x) - √(x + 1) = f x from rfl, ← h₂]
    refine StrictAntiOn.lt_iff_lt (s := Icc (-1) 3) h₁ ?_ (by constructor <;> linarith)
    have k₁ : 0 < √31 := by positivity
    have k₂ : √31 < 6 := (Real.sqrt_lt' (by simp)).2 (by norm_num)
    constructor <;> linarith
  have h₃ (x : ℝ) : -1 ≤ x ↔ 0 ≤ x + 1 := neg_le_iff_add_nonneg
  ext x
  have h₄ (x : ℝ) : x < 1 - √31 / 8 → 0 ≤ 3 - x := by
    intro hx
    linarith [show 0 < √31 by positivity]
  simp only [mem_setOf_eq, mem_Ico]
  specialize H x
  specialize h₃ x
  specialize h₄ x
  tauto
