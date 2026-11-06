import Mathlib

open BigOperators Real Set

lemma lemma_1 (x : ℝ) : ⌊x⌋ ≤ x ∧ x < ⌊x⌋ + 1 := by
  constructor
  .
    exact Int.floor_le x
  ·
    have h2 : x < (⌊x⌋ : ℤ) + 1 := Int.lt_floor_add_one x
    exact_mod_cast h2


theorem algebra_12605 : range (λ x => ⌊x⌋ - x) = {y | -1 < y ∧ y ≤ 0} := by
  ext y
  simp only [mem_range, mem_setOf_eq, exists_prop]
  constructor
  · -- First, prove that if y is in the range, then -1 < y ≤ 0.
    rintro ⟨x, hx⟩
    have h1 : ⌊x⌋ ≤ x := by
      exact Int.floor_le x
    have h2 : x < ⌊x⌋ + 1 := by
      exact Int.lt_floor_add_one x
    have h3 : -1 < y := by
      have h4 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast h1
      have h5 : x < (⌊x⌋ + 1 : ℝ) := by exact_mod_cast h2
      nlinarith
    have h4 : y ≤ 0 := by
      have h5 : (⌊x⌋ : ℝ) ≤ x := by exact_mod_cast h1
      nlinarith
    constructor <;> nlinarith
  · -- Now, prove the converse: if -1 < y ≤ 0, then there exists x such that y = ⌊x⌋ - x
    rintro ⟨hy1, hy2⟩
    use -y
    have h10 : ⌊-y⌋ = 0 := by
      have h11 : -1 < y := by linarith
      have h12 : 0 ≤ -y := by nlinarith
      have h13 : -y < 1 := by nlinarith
      rw [Int.floor_eq_iff]
      constructor <;> (try norm_num) <;> nlinarith
    simp [h10]
    all_goals nlinarith