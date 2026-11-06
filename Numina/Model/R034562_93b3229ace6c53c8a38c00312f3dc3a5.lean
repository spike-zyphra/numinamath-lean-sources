import Mathlib

open Real Set

theorem algebra_12557 : IsLeast {x : ℝ | ∃ (a b c d e f : ℝ), 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f ∧ a + b + c + d + e + f = 7 ∧ x = 1 / a + 4 / b + 9 / c + 16 / d + 25 / e + 36 / f} 63 := by
  constructor
  · -- Show that 63 is achievable.
    use 1 / 3, 2 / 3, 1, 4 / 3, 5 / 3, 2
    norm_num
  · -- Show that 63 is minimal.
    intro x hx
    rcases hx with ⟨a, b, c, d, e, f, ha, hb, hc, hd, he, hf, h1, hx⟩
    have h2 : 1 / a + 4 / b + 9 / c + 16 / d + 25 / e + 36 / f ≥ 63 := by
      have h4 : a + b + c + d + e + f = 7 := h1
      have h7 : 1 / a + 9 * a ≥ 6 := by
        have h10 : a > 0 := ha
        have h11 : 1 / a + 9 * a - 6 ≥ 0 := by
          have h12 : 1 / a + 9 * a - 6 = (3 * a - 1) ^ 2 / a := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * a - 1) ^ 2 ≥ 0 := sq_nonneg (3 * a - 1)
          have h14 : (3 * a - 1) ^ 2 / a ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      have h7' : 4 / b + 9 * b ≥ 12 := by
        have h10 : b > 0 := hb
        have h11 : 4 / b + 9 * b - 12 ≥ 0 := by
          have h12 : 4 / b + 9 * b - 12 = (3 * b - 2) ^ 2 / b := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * b - 2) ^ 2 ≥ 0 := sq_nonneg (3 * b - 2)
          have h14 : (3 * b - 2) ^ 2 / b ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      have h7'' : 9 / c + 9 * c ≥ 18 := by
        have h10 : c > 0 := hc
        have h11 : 9 / c + 9 * c - 18 ≥ 0 := by
          have h12 : 9 / c + 9 * c - 18 = (3 * c - 3) ^ 2 / c := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * c - 3) ^ 2 ≥ 0 := sq_nonneg (3 * c - 3)
          have h14 : (3 * c - 3) ^ 2 / c ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      have h7''' : 16 / d + 9 * d ≥ 24 := by
        have h10 : d > 0 := hd
        have h11 : 16 / d + 9 * d - 24 ≥ 0 := by
          have h12 : 16 / d + 9 * d - 24 = (3 * d - 4) ^ 2 / d := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * d - 4) ^ 2 ≥ 0 := sq_nonneg (3 * d - 4)
          have h14 : (3 * d - 4) ^ 2 / d ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      have h7'''' : 25 / e + 9 * e ≥ 30 := by
        have h10 : e > 0 := he
        have h11 : 25 / e + 9 * e - 30 ≥ 0 := by
          have h12 : 25 / e + 9 * e - 30 = (3 * e - 5) ^ 2 / e := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * e - 5) ^ 2 ≥ 0 := sq_nonneg (3 * e - 5)
          have h14 : (3 * e - 5) ^ 2 / e ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      have h7''''' : 36 / f + 9 * f ≥ 36 := by
        have h10 : f > 0 := hf
        have h11 : 36 / f + 9 * f - 36 ≥ 0 := by
          have h12 : 36 / f + 9 * f - 36 = (3 * f - 6) ^ 2 / f := by
            field_simp
            ring
          rw [h12]
          have h13 : (3 * f - 6) ^ 2 ≥ 0 := sq_nonneg (3 * f - 6)
          have h14 : (3 * f - 6) ^ 2 / f ≥ 0 := by
            apply div_nonneg
            linarith
            linarith
          linarith
        linarith
      linarith [h7, h7', h7'', h7''', h7'''', h7''''']
    linarith [hx, h2]