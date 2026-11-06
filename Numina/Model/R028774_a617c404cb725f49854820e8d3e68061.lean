import Mathlib

open Complex

theorem algebra_197494 (z : ℕ → ℂ)
  (hz0 : z 0 = 0) (hzn : ∀ n, z (n + 1) = z n ^ 2 + I) :
  abs (z 110) = Real.sqrt 2 := by

  have h1 : ∀ n, z (n + 1) = z n ^ 2 + I := hzn

  -- Compute z2 = -1 + I
  have h4 : z 2 = -1 + I := by
    rw [h1 1, h1 0, hz0]
    simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
    all_goals norm_num

  -- Induction hypothesis to determine the cycle
  have h7 : ∀ k, z (2 * k + 2) = -1 + I := by
    intro k
    induction k with
    | zero =>
      norm_num
      all_goals try { tauto }
      all_goals try { tauto }
      all_goals try { tauto }
    | succ k ih =>
      have h11 : 2 * (k + 1) + 2 = 2 * k + 4 := by ring
      rw [h11]
      have h9 : z (2 * k + 4) = (z (2 * k + 3)) ^ 2 + I := by
        rw [h1 (2 * k + 3)]
      have h10 : z (2 * k + 3) = (z (2 * k + 2)) ^ 2 + I := by
        rw [h1 (2 * k + 2)]
      rw [h9, h10, ih]
      simp [pow_two, Complex.ext_iff, Complex.I_mul_I]
      all_goals norm_num
      <;> ring_nf <;> norm_num [Complex.ext_iff]

  -- Since 110 = 2 * 54 + 2, so z 110 = -1 + I
  have h8 : z 110 = -1 + I := by
    specialize h7 54
    norm_num at h7 ⊢
    try { tauto }
  
  rw [h8]
  simp [Complex.abs, Complex.normSq]
  all_goals ring_nf <;> norm_num
  <;> ring_nf <;> norm_num
  <;> try { tauto }
  <;> try { tauto }