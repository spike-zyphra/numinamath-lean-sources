import Mathlib

theorem algebra_210113 {a b : ℝ} (z : ℂ) (hz : z.re = a ∧ z.im = b) :
    Complex.abs (z - Complex.I) > Complex.abs (z + Complex.I) ↔ b < 0 := by
  rcases hz with ⟨ha, hb⟩
  have h1 : Complex.abs (z - Complex.I) = Real.sqrt (a ^ 2 + (b - 1) ^ 2) := by
    have h11 : (z - Complex.I).re = a := by
      simp [ha, hb, Complex.ext_iff]
      <;> try { norm_num [Complex.I_re, Complex.I_im, ha, hb] }
      <;> ring_nf
      <;> try { norm_num [ha, hb] }
    have h22 : (z - Complex.I).im = b - 1 := by
      simp [ha, hb, Complex.ext_iff]
      <;> try { norm_num [Complex.I_re, Complex.I_im, ha, hb] }
      <;> ring_nf
      <;> try { norm_num [ha, hb] }
    simp [Complex.abs, Complex.normSq, h11, h22]
    <;> ring_nf
  have h2 : Complex.abs (z + Complex.I) = Real.sqrt (a ^ 2 + (b + 1) ^ 2) := by
    have h33 : (z + Complex.I).re = a := by
      simp [ha, hb, Complex.ext_iff]
      <;> try { norm_num [Complex.I_re, Complex.I_im, ha, hb] }
      <;> ring_nf
      <;> try { norm_num [ha, hb] }
    have h44 : (z + Complex.I).im = b + 1 := by
      simp [ha, hb, Complex.ext_iff]
      <;> try { norm_num [Complex.I_re, Complex.I_im, ha, hb] }
      <;> ring_nf
      <;> try { norm_num [ha, hb] }
    simp [Complex.abs, Complex.normSq, h33, h44]
    <;> ring_nf
  rw [h1, h2]
  constructor
  · -- Forward: If Complex.abs (z - i) > Complex.abs (z + i), then b < 0
    intro h
    have h3 : a ^ 2 + (b - 1) ^ 2 > a ^ 2 + (b + 1) ^ 2 := by
      have h4 : Real.sqrt (a ^ 2 + (b - 1) ^ 2) > Real.sqrt (a ^ 2 + (b + 1) ^ 2) := h
      have h5 : a ^ 2 + (b - 1) ^ 2 ≥ 0 := by nlinarith
      have h6 : a ^ 2 + (b + 1) ^ 2 ≥ 0 := by nlinarith
      have h7 : Real.sqrt (a ^ 2 + (b - 1) ^ 2) > Real.sqrt (a ^ 2 + (b + 1) ^ 2) := h4
      have h8 : a ^ 2 + (b - 1) ^ 2 > a ^ 2 + (b + 1) ^ 2 := by
        by_contra h9
        push_neg at h9
        have h9' : Real.sqrt (a ^ 2 + (b - 1) ^ 2) ≤ Real.sqrt (a ^ 2 + (b + 1) ^ 2) := by
          apply Real.sqrt_le_sqrt
          linarith
        linarith
      linarith
    nlinarith
  · -- Backward: If b < 0, then Complex.abs (z - i) > Complex.abs (z + i)
    intro h
    have h3 : a ^ 2 + (b - 1) ^ 2 > a ^ 2 + (b + 1) ^ 2 := by
      nlinarith
    have h4 : Real.sqrt (a ^ 2 + (b - 1) ^ 2) > Real.sqrt (a ^ 2 + (b + 1) ^ 2) := by
      apply Real.sqrt_lt_sqrt
      all_goals nlinarith
    linarith