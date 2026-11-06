import Mathlib

/- What is the value of the expression \([a] + [-a]\) when \(a\) is a real number, where \([x]\) denotes the greatest integer less than or equal to \(x\)?
case 1. a is integer -/
theorem number_theory_4846_1 (a : ℝ) (ha : a ∈ Set.range Int.cast) : ⌊a⌋ + ⌊-a⌋ = 0 := by
  --  1. **Case 1: \(a\) is an integer.**
  --  - If \(a\) is an integer, then \([a] = a\) and \([-a] = -a\).
  --  - Therefore, \([a] + [-a] = a + (-a) = 0\).
  obtain ⟨y, rfl⟩ := ha
  rw [show -(y:ℝ)=((-y : ℤ) : ℝ) from Eq.symm (Int.cast_neg y),
    Int.floor_intCast, Int.floor_intCast, add_neg_cancel]

/- What is the value of the expression \([a] + [-a]\) when \(a\) is a real number, where \([x]\) denotes the greatest integer less than or equal to \(x\)?
case 2. a is not integer -/
theorem number_theory_4846_2 (a : ℝ) (ha : a ∉ Set.range Int.cast) : ⌊a⌋ + ⌊-a⌋ = -1 := by
  --  2. **Case 2: \(a\) is not an integer.**
  --  - If \(a\) is not an integer, we can express \(a\) as \(n + f\), where \(n\) is the greatest integer less than \(a\) (i.e., \([a] = n\)) and \(f\) is the fractional part of \(a\) (where \(0 < f < 1\)).
  --  - In this case, \([-a] = -n - 1\) because \(-a = -n - f\) and the greatest integer less than \(-a\) is \(-n - 1\).
  --  - Thus, \([a] + [-a] = n + (-n - 1) = -1\).
  set f := a - ⌊a⌋ with hf
  rw [show  -a = - f + Int.cast (-⌊a⌋ : ℤ) by push_cast; ring, Int.floor_add_int]
  simp
  rw [Int.floor_eq_iff]
  simp
  constructor
  . rw [le_iff_lt_or_eq]
    constructor
    . linarith [Int.lt_floor_add_one a]
  rw [← Ne.le_iff_lt]
  linarith [Int.floor_le a]
  . intro h
    simp at ha
    refine ha ⌊a⌋ ?_
    rw [← h] at hf
    linarith
