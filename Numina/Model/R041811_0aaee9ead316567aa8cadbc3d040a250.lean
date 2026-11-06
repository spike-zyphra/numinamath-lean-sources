import Mathlib

open Complex

theorem algebra_163405 : IsLeast {x : ℝ | ∃ z w : ℂ, abs z = 1 ∧ abs w = 1 ∧ 1 ≤ abs (z + w) ∧ abs (z + w) ≤ √2 ∧ x = abs (z - w)} √2 := by
  constructor
  · -- Show that √2 is in the set.
    use 1, Complex.I
    constructor
    · -- |1| = 1
      simp [Complex.abs, Complex.normSq]
    constructor
    · -- |i| = 1
      simp [Complex.abs, Complex.normSq]
    constructor
    · -- Show 1 ≤ |1 + i|
      have h1 : abs ((1 : ℂ) + Complex.I) = Real.sqrt 2 := by
        simp [Complex.abs, Complex.normSq]
        all_goals
          ring_nf
      rw [h1]
      have h2 : 1 ≤ Real.sqrt 2 := by
        rw [Real.le_sqrt] <;> norm_num
      linarith
    constructor
    · -- Show |1 + i| ≤ √2
      have h1 : abs ((1 : ℂ) + Complex.I) = Real.sqrt 2 := by
        simp [Complex.abs, Complex.normSq]
        all_goals
          ring_nf
      rw [h1]
      all_goals
        norm_num
    · -- Show √2 = |1 - i|
      have h2 : abs ((1 : ℂ) - Complex.I) = Real.sqrt 2 := by
        simp [Complex.abs, Complex.normSq]
        all_goals
          ring_nf
      rw [h2]
  · -- Show that √2 is the smallest element.
    intro x hx
    rcases hx with ⟨z, w, h1, h2, h3, h4, hx⟩
    have h5 : abs z = 1 := h1
    have h6 : abs w = 1 := h2
    have h7 : 1 ≤ abs (z + w) := h3
    have h8 : abs (z + w) ≤ Real.sqrt 2 := h4
    have h9 : x = abs (z - w) := hx
    have h10 : abs (z - w) ≥ Real.sqrt 2 := by
      have h100 : abs (z - w) ^ 2 + abs (z + w) ^ 2 = 4 := by
        have h101 : abs (z - w) ^ 2 = (z - w).re ^ 2 + (z - w).im ^ 2 := by
          have h0 : abs (z - w) = Real.sqrt ((z - w).re ^ 2 + (z - w).im ^ 2) := by
            simp [Complex.abs, Complex.normSq]
            <;> ring_nf
          rw [h0]
          rw [Real.sq_sqrt (by positivity)]
        have h102 : abs (z + w) ^ 2 = (z + w).re ^ 2 + (z + w).im ^ 2 := by
          have h0 : abs (z + w) = Real.sqrt ((z + w).re ^ 2 + (z + w).im ^ 2) := by
            simp [Complex.abs, Complex.normSq]
            <;> ring_nf
          rw [h0]
          rw [Real.sq_sqrt (by positivity)]
        have h103 : z.re ^ 2 + z.im ^ 2 = 1 := by
          have h0 : abs z = 1 := h1
          have h100 : abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
            simp [Complex.abs, Complex.normSq]
            all_goals
              ring_nf
          rw [h100] at h0
          have h200 : Real.sqrt (z.re ^ 2 + z.im ^ 2) = 1 := h0
          have h201 : z.re ^ 2 + z.im ^ 2 = 1 := by
            calc
              z.re ^ 2 + z.im ^ 2 = (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 := by
                rw [Real.sq_sqrt]
                positivity
              _ = 1 ^ 2 := by
                rw [h200]
              _ = (1 : ℝ) := by
                norm_num
          linarith
        have h104 : w.re ^ 2 + w.im ^ 2 = 1 := by
          have h0 : abs w = 1 := h2
          have h100 : abs w = Real.sqrt (w.re ^ 2 + w.im ^ 2) := by
            simp [Complex.abs, Complex.normSq]
            all_goals
              ring_nf
          rw [h100] at h0
          have h200 : Real.sqrt (w.re ^ 2 + w.im ^ 2) = 1 := h0
          have h201 : w.re ^ 2 + w.im ^ 2 = 1 := by
            calc
              w.re ^ 2 + w.im ^ 2 = (Real.sqrt (w.re ^ 2 + w.im ^ 2)) ^ 2 := by
                rw [Real.sq_sqrt]
                positivity
              _ = 1 ^ 2 := by
                rw [h200]
              _ = (1 : ℝ) := by
                norm_num
          linarith
        have h1000 : (z - w).re = z.re - w.re := by
          simp [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.I_re]
        have h1001 : (z - w).im = z.im - w.im := by
          simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.I_im]
        have h1002 : (z + w).re = z.re + w.re := by
          simp [Complex.add_re, Complex.ofReal_re, Complex.I_re]
        have h1003 : (z + w).im = z.im + w.im := by
          simp [Complex.add_im, Complex.ofReal_im, Complex.I_im]
        rw [h101, h102, h1000, h1001, h1002, h1003]
        nlinarith [h103, h104]
      have h1000 : abs (z - w) ^ 2 ≥ 2 := by
        have h1001 : abs (z - w) ^ 2 + abs (z + w) ^ 2 = 4 := h100
        have h1002 : abs (z + w) ^ 2 ≤ 2 := by
          have h1003 : abs (z + w) ≤ Real.sqrt 2 := h8
          have h1004 : abs (z + w) ^ 2 ≤ (Real.sqrt 2) ^ 2 := by
            nlinarith [h1003, Real.sqrt_nonneg 2]
          have h1005 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
          nlinarith [h1005, h1004]
        nlinarith
      have h1001 : abs (z - w) ≥ 0 := by
        positivity
      have h1004 : abs (z - w) ≥ Real.sqrt 2 := by
        have h1005 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
        nlinarith [Real.sqrt_nonneg 2, sq_nonneg (abs (z - w) - Real.sqrt 2)]
      linarith
    linarith [h10, h9]