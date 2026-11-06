import Mathlib

/- If $y>0$, find the range of all possible values of $y$ such that $\lceil{y}\rceil\cdot\lfloor{y}\rfloor=42$.  Express your answer using interval notation. -/
theorem algebra_22038 (y : ℝ) (hy : y > 0) :
    ⌈y⌉ * ⌊y⌋ = 42 ↔ y ∈ Set.Ioo 6 7 := by
  constructor
  -- if $\lceil y\rceil\cdot\lfloor y\rfloor = 42$ then $y \in (6, 7)$
  intro yyeq
  constructor
  · -- we prove $y > 6$
    by_contra contra
    -- for otherwise, $y \leq 6$, so $\lceil y\rceil\cdot\lfloor y\rfloor \leq 36$, a contradiction
    rw [not_lt] at contra
    have floorle : ⌊y⌋ ≤ 6 := by
      have floorle : ⌊y⌋ ≤ ⌊(6 : ℝ)⌋ := by
        exact Int.floor_le_floor contra
      rw [Int.floor_ofNat] at floorle
      exact floorle
    have ceille : ⌈y⌉ ≤ 6 := by
      have ceille : ⌈y⌉ ≤ ⌈(6 : ℝ)⌉ := by
        exact Int.ceil_le_ceil contra
      rw [Int.ceil_ofNat] at ceille
      exact ceille
    have le : ⌈y⌉ * ⌊y⌋ ≤ 6 * 6 := by
      apply mul_le_mul
      exact ceille
      exact floorle
      have floorge : ⌊(0 : ℝ)⌋ ≤ ⌊y⌋ := by
        exact Int.floor_le_floor (by linarith)
      rw [Int.floor_zero] at floorge
      exact floorge
      norm_num
    linarith
  · -- we prove $y < 7$
    by_contra contra
    -- for otherwise, $y \geq 7$, so $\lceil y\rceil\cdot\lfloor y\rfloor \geq 49$, a contradiction
    rw [not_lt] at contra
    have floorle : 7 ≤ ⌊y⌋ := by
      have floorle : ⌊(7 : ℝ)⌋ ≤ ⌊y⌋ := by
        exact Int.floor_le_floor contra
      rw [Int.floor_ofNat] at floorle
      exact floorle
    have ceille : 7 ≤ ⌈y⌉ := by
      have ceille : ⌈(7 : ℝ)⌉ ≤ ⌈y⌉ := by
        exact Int.ceil_le_ceil contra
      rw [Int.ceil_ofNat] at ceille
      exact ceille
    have le : 7 * 7 ≤ ⌈y⌉ * ⌊y⌋ := by
      apply mul_le_mul
      exact ceille
      exact floorle
      norm_num
      have ceilge : ⌈(0 : ℝ)⌉ ≤ ⌈y⌉ := by
        exact Int.ceil_le_ceil (by linarith)
      rw [Int.ceil_zero] at ceilge
      exact ceilge
    linarith
  -- if $y \in (6, 7), then $\lceil y\rceil\cdot\lfloor y\rfloor = 42$
  intro yin
  rw [Set.mem_Ioo] at yin
  have flooreq : ⌊y⌋ = 6 := by
    refine Int.floor_eq_iff.mpr ?_
    simp only [Int.cast_ofNat]
    constructor
    any_goals
    linarith
  have ceileq : ⌈y⌉ = 7 := by
    refine Int.ceil_eq_iff.mpr ?_
    simp only [Int.cast_ofNat]
    constructor
    any_goals
    linarith
  norm_num [flooreq, ceileq]