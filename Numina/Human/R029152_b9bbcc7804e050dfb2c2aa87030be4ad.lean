import Mathlib

/-
Show that if $ a $ is a real number, then $ \lfloor a \rfloor + \lfloor a + \frac{1}{2} \rfloor = \lfloor 2a \rfloor $.
-/
theorem number_theory_4902 (a : ℝ) : ⌊a⌋ + ⌊a + 1 / 2⌋ = ⌊2 * a⌋ := by
  set n := ⌊a⌋
  set f := a - n
  by_cases h : f < 1 / 2

  -- case 1 : f < 1 / 2
  .
    -- calculating ⌊a + 1 / 2⌋
    have : ⌊a + 1 / 2⌋ = n := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith [Int.floor_le a]

    -- calculating ⌊2 * a⌋
    have : ⌊2 * a⌋ = 2 * n := by
      rw [Int.floor_eq_iff]
      constructor <;> (simp; linarith [Int.floor_le a])

    -- calculating result
    linarith

  -- case 2 : f ≥ 1 / 2
  . push_neg at h

    -- calculating ⌊a + 1 / 2⌋
    have : ⌊a + 1 / 2⌋ = n + 1 := by
      rw [Int.floor_eq_iff, show ↑(n + 1) = (n:ℝ) + 1 by simp]
      constructor <;> linarith [Int.floor_le a, Int.lt_floor_add_one a]

    -- calculating ⌊2 * a⌋
    have : ⌊2 * a⌋ = 2 * n + 1 := by
      rw [Int.floor_eq_iff]
      constructor <;> (simp; linarith [Int.floor_le a, Int.lt_floor_add_one a])

    -- calculating result
    linarith
