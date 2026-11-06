import Mathlib

/-Determine all rational numbers r such that the equation
rx^2 + (r+2)x + r - 1
has exactly integer roots.-/

lemma vieta_formula {p q x1 x2: ℚ} (ne: ¬x1 = x2) (h1: x1 ^ 2 + p * x1 + q = 0) (h2: x2 ^ 2 + p * x2 + q = 0):
    x1 + x2 = -p ∧ x1 * x2 = q := by

  have h: (x1 - x2) * (x1 + x2 + p) = 0 := by nlinarith
  replace ne: ¬ x1 - x2 = 0 := by
    by_contra! i
    replace i: x1 = x2 := by linarith
    simp [i] at ne
  simp [ne] at h
  constructor
  .
    linarith
  .
    have f: (x1 + x2) ^ 2 - 2 * (x1 * x2) + p * (x1 + x2) + 2 * q = 0 := by
      nlinarith
    replace h: x1 + x2 = -p := by linarith
    simp [h] at f
    nlinarith

theorem algebra_625819: {r: ℚ | ∃ x1 x2: ℤ, r * x1 ^ 2 + (r + 2) * x1 + r - 1 = 0 ∧
r * x2 ^ 2 + (r + 2) * x2 + r - 1 = 0 ∧ ∀ y: ℝ, r * y ^ 2 + (r + 2) * y + r - 1 = 0 → y = x1 ∨ y = x2}
  = {-1 / 3, 1} := by

  ext r
  simp only [Set.mem_setOf_eq]
  constructor

  -- the forward direction
  .
    intro h
    obtain ⟨x1, x2, h1, h2, hy⟩ := h
    simp
    by_cases l: x1 = x2

    -- case 1: x1 = x2
    .
      clear h2
      by_cases s: r = 0
      .
        simp [s] at h1
        norm_cast at h1
        replace h1: 2 * x1 = 1 := by linarith
        have c: 2 ∣ 1 := by
          zify
          rw [← h1]
          simp
        norm_num at c
      .
        let y:= -(r + 2) / r - x1

        -- we show that y is also an solution
        specialize hy y
        have u: r * y ^ 2 + (r + 2) * y + r - 1 = 0 := by
          simp [y]
          field_simp
          ring_nf
          rw [show -r ^ 3 + r ^ 3 * ↑x1 * 2 + r ^ 4 + r ^ 4 * ↑x1 + r ^ 4 * ↑x1 ^ 2
            = r ^ 3 * (r * x1 ^ 2 + (r + 2) * x1 + r - 1) by ring]
          simp [h1]
        rify at u
        simp [u] at hy
        simp [l] at hy
        simp [y] at hy
        simp [← l] at hy
        replace hy: x1 = -(r + 2) / (2 * r) := by
          rify
          field_simp
          field_simp at hy
          nlinarith
        simp [hy] at h1
        field_simp at h1
        ring_nf at h1
        rw [show -(r ^ 2 * 8) - r ^ 3 * 16 + r ^ 4 * 6  = 2 * r ^ 2 * (3 * r ^ 2 - 8 * r - 4) by ring] at h1
        simp [s] at h1

        -- so far we have shown that Δ = 0, then we need to show that ¬ r ∈ ℚ
        clear * - h1
        set s:= 3 / 2 * (r - 4 / 3)
        have hs: r = 2 / 3 * s + 4 / 3 := by
          simp [s]
          ring
        simp [hs] at h1
        clear_value s
        clear hs
        ring_nf at h1
        replace h1: s ^ 2 - 7 = 0 := by
          nlinarith
        have eq: s ^ 2 - 7 = (s - √7) * (s + √7) := by
          ring_nf
          have c: √7 ^ 2 = 7 := by
            symm
            rw [← Real.sqrt_eq_iff_eq_sq]
            norm_num
            apply Real.sqrt_nonneg
          simp [c]
          ring
        rify at h1
        rw [eq] at h1
        clear eq
        simp at h1
        rcases h1 with h1 | h1
        .
          replace h1: s = √7 := by linarith
          have c: Irrational √(7: ℝ) := by
            rw [show (7: ℝ) = ↑(7: ℕ) by simp]
            rw [irrational_sqrt_natCast_iff]
            native_decide
          rw [← h1] at c
          absurd c
          simp
        .
          let v:= -s
          replace h1: v = √7 := by simp [v]; linarith
          clear_value v
          have c: Irrational √(7: ℝ) := by
            rw [show (7: ℝ) = ↑(7: ℕ) by simp]
            rw [irrational_sqrt_natCast_iff]
            native_decide
          rw [← h1] at c
          absurd c
          simp


    -- case 2: x1 ≠ x2
    .
      clear hy
      by_cases s: r = 0
      .
        simp [s] at h1
        norm_cast at h1
        replace h1: 2 * x1 = 1 := by linarith
        have c: 2 ∣ 1 := by
          zify
          rw [← h1]
          simp
        norm_num at c
      .
        replace h1:x1 ^ 2 + (r + 2) / r * x1 + (r - 1) / r = 0 := by
          field_simp
          nlinarith
        replace h2:x2 ^ 2 + (r + 2) / r * x2 + (r - 1) / r = 0 := by
          field_simp
          nlinarith

        -- then we can apply Vieta's formula
        replace l: ¬ (x1: ℚ) = x2 := by
          simp [l]
        have h:= vieta_formula l h1 h2
        clear h1 h2
        rcases h with ⟨h1, h2⟩

        -- then we eliminate r
        have h: 4 * (x1 * x2) - 2 * (x1 + x2) + 1 = 7 := by
          qify
          rw [h1, h2]
          field_simp
          ring
        rw [show 4 * (x1 * x2) - 2 * (x1 + x2) + 1 = (2 * x1 - 1) * (2 * x2 - 1) by ring] at h
        have o: (2 * x1 - 1).natAbs ∣ 7 := by
          rw [show 7 = (7: ℤ).natAbs by simp]
          rw [Int.natAbs_dvd_natAbs]
          rw [← h]
          simp
        replace o: (2 * x1 - 1).natAbs ∈ Nat.divisors 7 := by
          simp
          exact o
        rw [show Nat.divisors 7 = {1, 7} by rfl] at o
        simp at o
        zify at o
        by_cases i: 0 < x1

        -- case 1: x1 > 0
        .
          rw [show |2 * x1 - 1| = 2 * x1 - 1 by apply abs_of_nonneg; linarith] at o
          rcases o with o | o
          .
            replace o: x1 = 1 := by nlinarith
            simp [o] at h
            have v: x2 = 4 := by nlinarith
            simp [o, v] at h1
            field_simp at h1
            replace h1: r = -1 / 3 := by
              nlinarith
            simp [h1]
          .
            replace o: x1 = 4 := by nlinarith
            simp [o] at h
            have v: x2 = 1 := by nlinarith
            simp [o, v] at h2
            field_simp at h2
            replace h2: r = -1 / 3 := by
              nlinarith
            simp [h2]

        -- case 2: x1 < 0
        .
          rw [show |2 * x1 - 1| = -(2 * x1 - 1) by apply abs_of_neg; linarith] at o
          rcases o with o | o
          .
            replace o: x1 = 0 := by nlinarith
            simp [o] at h
            have v: x2 = -3:= by nlinarith
            simp [o, v] at h1
            field_simp at h1
            replace h1: r = 1 := by
              nlinarith
            simp [h1]
          .
            replace o: x1 = -3 := by nlinarith
            simp [o] at h
            have v: x2 = 0 := by nlinarith
            simp [o, v] at h2
            field_simp at h2
            replace h2: r = 1 := by
              nlinarith
            simp [h2]


  -- the backward direction
  .
    intro h
    simp at h
    rcases h with h | h
    .
      simp [h]
      use 4
      norm_num
      use 1
      norm_num
      intro y h
      field_simp at h
      ring_nf at h
      rw [show -36 + (y * 45 - y ^ 2 * 9) = -9 * (y - 4) * (y - 1) by ring] at h
      simp at h
      rcases h with h | h
      .
        left
        linarith
      .
        right
        linarith
    .
      simp [h]
      use 0
      norm_num
      use -3
      norm_num
      intro y h
      rw [show y ^ 2 + 3 * y = y * (y + 3) by ring] at h
      simp at h
      rcases h with h | h
      .
        left
        linarith
      .
        right
        linarith