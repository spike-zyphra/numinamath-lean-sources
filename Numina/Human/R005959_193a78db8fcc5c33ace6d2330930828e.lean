import Mathlib

open ProbabilityTheory MeasureTheory Set

theorem combinatorics_610920 :
  (uniformOn ({1,2,3,4,5,6} ×ˢ {1,2,3,4,5,6})) {(x,y) | (x+y)%5=0} = 7/36 := by

  let A: Set ℕ := {1,2,3,4,5,6}
  let AxA := A ×ˢ A
  let B: Set (ℕ × ℕ) := {(x,y) | (x+y)%5=0}
  let C := AxA ∩ B

  have hsf : Finite A := by
    unfold A
    apply Finite.ofFinset (Finset.Icc 1 6)
    simp
    intro x
    constructor
    . intro ⟨h1, h2⟩
      interval_cases x
      any_goals simp
    . intro h
      aesop
  have hsf1: Finite (A ×ˢ A) := by
    apply Set.Finite.prod
    all_goals exact hsf
  have hsf2: Finite C := by
    apply Set.Finite.inter_of_left
    exact hsf1

  have h2: (Finite.toFinset hsf2).card = 7 := by
    simp [Finite.measurableSet, C, AxA, A, B]
    rw [Finset.card_filter]
    decide

  simp [uniformOn]
  rw [cond_apply, Measure.count_apply_finite (AxA) hsf1, Measure.count_apply_finite C hsf2, h2]
  simp [Finset.coe_filter_univ]
  rw [ENNReal.eq_div_iff, ← mul_assoc, ENNReal.mul_inv_cancel]
  all_goals try simp
  apply Set.Finite.measurableSet hsf1
