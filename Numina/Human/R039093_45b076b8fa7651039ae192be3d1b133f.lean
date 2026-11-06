import Mathlib

theorem algebra_12981 : IsGreatest {(x : ℝ) | ⌊x⌋ = 5 + 100 * (x - ⌊x⌋)} 104.99 := by
  rw [IsGreatest]
  constructor
  . simp only [Set.mem_setOf_eq]
    have h : ⌊(104.99 : ℝ)⌋ = 104 := by
      rw [Int.floor_eq_iff];
      constructor <;> norm_num
    rw [h]
    norm_num
  . intro x hx
    simp at hx
    have hx1 : x = (101 * ⌊x⌋ - 5) / 100 := by
      rw [Int.fract] at hx
      linarith only [hx]
    have hx2 : ⌊x⌋ ≤ 104 := by
      have ha : Int.fract x < 1 := by
        exact Int.fract_lt_one x
      have ha2 : (⌊x⌋ : ℝ) < 105 := by
        linarith only [hx, ha]
      norm_cast at ha2
      exact Int.lt_add_one_iff.mp ha2
    rify at hx2
    linarith only [hx1, hx2]
