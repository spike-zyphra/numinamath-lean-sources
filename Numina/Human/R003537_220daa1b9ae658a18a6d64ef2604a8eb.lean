import Mathlib

/- For a known number k, the product of the roots of the equation
x^2− 3kx+2k^2 −1=0 is 7, then all the roots are
(A) positive integers. (B) negative integers. (C) rational numbers but not integers. (D) irrational numbers.
(E) imaginary numbers.-/

theorem algebra_192945 {k: ℝ} (x1 x2: ℂ) (h1: x1 ^ 2 - 3 * k * x1 + 2 * k ^ 2 - 1 = 0)
  (h2: x2 ^ 2 - 3 * k * x2 + 2 * k ^ 2 - 1 = 0)
  (h3: x1 * x2 = 7): ∃ a b: ℝ, Irrational a ∧ Irrational b ∧ x1 = a ∧ x2 = b := by

  by_cases ne: x1 = x2

  --case 1: x1 = x2
  .
    simp [ne] at *
    replace h3: x2 * x2 - 7 = 0 := by
      rw [h3]
      simp
    have eq: x2 * x2 - 7 = (x2 - √7) * (x2 + √7) := by
      ring_nf
      have eq: (√7: ℂ) ^ 2 = 7 := by
        norm_cast
        symm
        rw [← Real.sqrt_eq_iff_eq_sq]
        linarith
        apply Real.sqrt_nonneg
      rw [eq]
      ring
    rw [eq] at h3
    clear eq
    simp at h3
    rcases h3 with h3 | h3
    .
      replace h3: x2 = √7 := by
        rw [show x2 = x2 - √7 + √7 by ring]
        rw [h3]
        simp
      use √7
      have o: Irrational (√7: ℝ) := by
        rw [show (7: ℝ) = ↑(7: ℕ) by simp]
        rw [irrational_sqrt_natCast_iff]
        native_decide
      simp [o]
      use √7
    .
      replace h3: x2 = -√7 := by
        rw [show x2 = x2 + √7 - √7 by ring]
        rw [h3]
        simp
      use -√7
      have o: Irrational (-√7: ℝ) := by
        rw [show (7: ℝ) = ↑(7: ℕ) by simp]
        apply Irrational.neg
        rw [irrational_sqrt_natCast_iff]
        native_decide
      simp [o]
      use -√7
      simp [o]
      exact h3

  --case 2: x1 ≠ x2
  .
    -- we show vieta's relations
    have h4: x1 * x2 = 2 * k ^ 2 - 1 := by
      have l: x1 ^ 2 - 3 * k * x1 + 2 * k ^ 2 - 1 - (x2 ^ 2 - 3 * k * x2 + 2 * k ^ 2 - 1) = 0 := by
        rw [h1]
        rw [h2]
        ring
      have eq: x1 ^ 2 - 3 * k * x1 + 2 * k ^ 2 - 1 - (x2 ^ 2 - 3 * k * x2 + 2 * k ^ 2 - 1)
        = (x1 - x2) * (x1 + x2 - 3 * k) := by
        ring
      rw [eq] at l
      simp at l
      rcases l with l | l
      .
        replace l: x1 = x2 := by
          rw [show x1 = x1 - x2 + x2 by ring]
          rw [l]
          simp
        simp [l] at ne
      .
        replace l: x1 + x2 = 3 * k := by
          rw [show x1 + x2 = x1 + x2 - 3 * k + 3 * k by ring]
          rw [l]
          simp
        have f: x1 ^ 2 - 3 * k * x1 + 2 * k ^ 2 - 1 + (x2 ^ 2 - 3 * k * x2 + 2 * k ^ 2 - 1) = 0 := by
          rw [h1]
          rw [h2]
          ring
        have eq: x1 ^ 2 - 3 * k * x1 + 2 * k ^ 2 - 1 + (x2 ^ 2 - 3 * k * x2 + 2 * k ^ 2 - 1)
                = (x1 + x2) ^ 2 - 2 * (x1 * x2) - 3 * k * (x1 + x2) + 4 * k ^ 2 - 2 := by
                ring
        rw [eq] at f
        clear eq
        simp [l] at f
        set p:= x1 * x2
        clear * - f
        clear_value p
        ring_nf at f
        replace f: 2 * p = -2 + (k ^ 2 * 4) := by
          rw [show 2 * p = (-2 + ↑k ^ 2 * 4) - (-2 + (↑k ^ 2 * 4 - p * 2)) by ring]
          rw [f]
          ring
        rw [show p = 2 * p / 2 by ring]
        rw [f]
        ring

    rw [h4] at h3
    norm_cast at h3
    replace h3: (k - 2) * (k + 2) = 0 := by nlinarith
    simp at h3
    rcases h3 with h3 | h3

    -- case 1: k = -2
    .
      replace h3: k = 2 := by
        nlinarith
      simp [h3] at h1 h2
      norm_num at h1 h2
      have eq: x1 ^ 2 - 6 * x1 + 8 - 1 = (x1 - (3 + √2)) * (x1 - (3 - √2)) := by
        ring_nf
        have eq: (√2: ℂ) ^ 2 = 2 := by
          norm_cast
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply Real.sqrt_nonneg
        rw [eq]
        ring
      rw [eq] at h1
      simp at h1
      clear eq
      have eq: x2 ^ 2 - 6 * x2 + 8 - 1 = (x2 - (3 + √2)) * (x2 - (3 - √2)) := by
        ring_nf
        have eq: (√2: ℂ) ^ 2 = 2 := by
          norm_cast
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply Real.sqrt_nonneg
        rw [eq]
        ring
      rw [eq] at h2
      simp at h2
      clear eq
      rcases h1 with h1 | h1
      .
        replace h1: x1 = 3 + √2 := by
          rw [show x1 = x1 - (3 + √2) + (3 + √2) by ring]
          rw [h1]
          simp
        rcases h2 with h2 | h2
        .
          replace h2: x2 = 3 + √2 := by
            rw [show x2 = x2 - (3 + √2) + (3 + √2) by ring]
            rw [h2]
            simp
          absurd ne
          simp [h1, h2]
        .
          replace h2: x2 = 3 - √2 := by
            rw [show x2 = x2 - (3 - √2) + (3 - √2) by ring]
            rw [h2]
            simp
          use 3 + √2
          use 3 - √2
          constructor
          .
            rw [show (3: ℝ) + √2 = √2 + ↑(3: ℤ) by simp; linarith]
            apply Irrational.add_int
            rw [show (2: ℝ) = ↑(2: ℕ) by simp]
            rw [irrational_sqrt_natCast_iff]
            native_decide
          .
            constructor
            .
              rw [show (3: ℝ) - √2 = -√2 + ↑(3: ℤ) by simp; linarith]
              apply Irrational.add_int
              rw [show (2: ℝ) = ↑(2: ℕ) by simp]
              apply Irrational.neg
              rw [irrational_sqrt_natCast_iff]
              native_decide
            .
              constructor
              .
                simp [h1]
              .
                simp [h2]
      .
        replace h1: x1 = 3 - √2 := by
          rw [show x1 = x1 - (3 - √2) + (3 - √2) by ring]
          rw [h1]
          simp
        rcases h2 with h2 | h2
        .
          replace h2: x2 = 3 + √2 := by
            rw [show x2 = x2 - (3 + √2) + (3 + √2) by ring]
            rw [h2]
            simp
          use 3 - √2
          use 3 + √2
          constructor
          .
            rw [show (3: ℝ) - √2 = -√2 + ↑(3: ℤ) by simp; linarith]
            apply Irrational.add_int
            rw [show (2: ℝ) = ↑(2: ℕ) by simp]
            apply Irrational.neg
            rw [irrational_sqrt_natCast_iff]
            native_decide
          .
            constructor
            .
              rw [show (3: ℝ) + √2 = √2 + ↑(3: ℤ) by simp; linarith]
              apply Irrational.add_int
              rw [show (2: ℝ) = ↑(2: ℕ) by simp]
              rw [irrational_sqrt_natCast_iff]
              native_decide
            .
              constructor
              .
                simp [h1]
              .
                simp [h2]
        .
          replace h2: x2 = 3 - √2 := by
            rw [show x2 = x2 - (3 - √2) + (3 - √2) by ring]
            rw [h2]
            simp
          absurd ne
          simp [h1, h2]

    -- case 2: k = 2
    .
      replace h3: k = -2 := by
        nlinarith
      simp [h3] at h1 h2
      norm_num at h1 h2
      have eq: x1 ^ 2 + 6 * x1 + 8 - 1 = (x1 + (3 + √2)) * (x1 + (3 - √2)) := by
        ring_nf
        have eq: (√2: ℂ) ^ 2 = 2 := by
          norm_cast
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply Real.sqrt_nonneg
        rw [eq]
        ring
      rw [eq] at h1
      simp at h1
      clear eq
      have eq: x2 ^ 2 + 6 * x2 + 8 - 1 = (x2 + (3 + √2)) * (x2 + (3 - √2)) := by
        ring_nf
        have eq: (√2: ℂ) ^ 2 = 2 := by
          norm_cast
          symm
          rw [← Real.sqrt_eq_iff_eq_sq]
          linarith
          apply Real.sqrt_nonneg
        rw [eq]
        ring
      rw [eq] at h2
      simp at h2
      clear eq
      rcases h1 with h1 | h1
      .
        replace h1: x1 = -3 - √2 := by
          rw [show x1 = x1 + (3 + √2) - (3 + √2) by ring]
          rw [h1]
          simp
          ring
        rcases h2 with h2 | h2
        .
          replace h2: x2 = -3 - √2 := by
            rw [show x2 = x2 + (3 + √2) - (3 + √2) by ring]
            rw [h2]
            simp
            ring
          absurd ne
          simp [h1, h2]
        .
          replace h2: x2 = -3 + √2 := by
            rw [show x2 = x2 + (3 - √2) - (3 - √2) by ring]
            rw [h2]
            simp
            ring
          use -3 - √2
          use -3 + √2
          constructor
          .
            rw [show (-3: ℝ) - √2 = -(√2 + ↑(3: ℤ)) by simp; linarith]
            apply Irrational.neg
            apply Irrational.add_int
            rw [show (2: ℝ) = ↑(2: ℕ) by simp]
            rw [irrational_sqrt_natCast_iff]
            native_decide
          .
            constructor
            .
              rw [show (-3: ℝ) + √2 = √2 + ↑(-3: ℤ) by simp; linarith]
              apply Irrational.add_int
              rw [show (2: ℝ) = ↑(2: ℕ) by simp]
              rw [irrational_sqrt_natCast_iff]
              native_decide
            .
              constructor
              .
                simp [h1]
              .
                simp [h2]
      .
        replace h1: x1 = -3 + √2 := by
          rw [show x1 = x1 + (3 - √2) - (3 - √2) by ring]
          rw [h1]
          simp
          ring
        rcases h2 with h2 | h2
        .
          replace h2: x2 = -3 - √2 := by
            rw [show x2 = x2 + (3 + √2) - (3 + √2) by ring]
            rw [h2]
            simp
            ring
          use -3 + √2
          use -3 - √2
          constructor
          .
            rw [show (-3: ℝ) + √2 = √2 + ↑(-3: ℤ) by simp; linarith]
            apply Irrational.add_int
            rw [show (2: ℝ) = ↑(2: ℕ) by simp]
            rw [irrational_sqrt_natCast_iff]
            native_decide
          .
            constructor
            .
              rw [show (-3: ℝ) - √2 = -√2 + ↑(-3: ℤ) by simp; linarith]
              apply Irrational.add_int
              rw [show (2: ℝ) = ↑(2: ℕ) by simp]
              apply Irrational.neg
              rw [irrational_sqrt_natCast_iff]
              native_decide
            .
              constructor
              .
                simp [h1]
              .
                simp [h2]
        .
          replace h2: x2 = -3 + √2 := by
            rw [show x2 = x2 + (3 - √2) - (3 - √2) by ring]
            rw [h2]
            simp
            ring
          absurd ne
          simp [h1, h2]