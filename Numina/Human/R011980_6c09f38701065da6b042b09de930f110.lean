import Mathlib

/-If real numbers x,y satisfy
4x+3y−2x[(x^2 + y^2) / x^2] = 0, then the value of y / x is
-/

theorem algebra_316091 {x y : ℝ} (hx : x ≠ 0)
    (h : 4 * x + 3 * y - 2 * x * ⌊(x ^ 2 + y ^ 2) / x ^ 2⌋ = 0) :
    y / x = -2 / 3 ∨ y / x = 2 := by

    set t:= (3 * y) / (2 * x)
    replace h: 2 + t - ⌊(x ^ 2 + y ^ 2) / x ^ 2⌋ = 0 := by
      simp [t]
      field_simp
      nlinarith
    have eq: ⌊(x ^ 2 + y ^ 2) / x ^ 2⌋ = 1 + ⌊y ^ 2 / x ^ 2⌋  := by
      rw [show (x ^ 2 + y ^ 2) / x ^ 2 = y ^ 2 / x ^ 2 + 1 by field_simp; ring]
      rw [Int.floor_add_one]
      ring
    rw [eq] at h
    clear eq
    rw [show y ^ 2 / x ^ 2 = 4 * t ^ 2 / 9 by simp [t]; field_simp; ring] at h
    rw [Int.cast_add] at h
    simp at h
    replace h: ↑⌊4 * t ^ 2 / 9⌋ = 1 + t := by nlinarith
    have l1: 1 + t ≤ 4 * t ^ 2 / 9 := by
      rw [← h]
      apply Int.floor_le
    have l2: 4 * t ^ 2 / 9 < 1 + t + 1 := by
      rw [← h]
      apply Int.lt_floor_add_one

    -- from h we see that t is integer
    set s:= ⌊4 * t ^ 2 / 9⌋
    simp [← h] at l1 l2
    replace h: t = s - 1 := by linarith
    simp [h] at l1 l2
    rw [show y / x = (2 * (s - 1)) / 3 by rw [← h]; simp [t]; field_simp; ring]

    --from l1, l2, we deduce that s = 0 ∨ 4
    replace l2: -1 < s ∧ s < 5 := by
      rify  -- due to l2
      constructor
      .
        nlinarith [l2]
      .
        nlinarith [l2]

    by_cases u: s < 1

    -- then s = 0
    .
      have o: s = 0 := by omega
      simp [o]

    -- then s = 4
    .
      simp at u
      have o: 4 ≤ s := by
        replace l1: 0 ≤ 4 * s ^ 2 - 17 * s + 4 := by
          rify
          nlinarith
        nlinarith
      replace o: s = 4 := by omega
      simp [o]
      norm_num
      