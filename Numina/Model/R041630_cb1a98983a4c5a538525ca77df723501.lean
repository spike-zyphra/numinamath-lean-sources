import Mathlib

open Complex Finset Polynomial

theorem algebra_235856 {z : ℕ → ℂ} (hz1 : z 1 = 1)
    (hzn : ∀ n ≥ 1, z (n + 1) = starRingEnd ℂ (z n) + 1 + n * .I) :
    z 2015 = 2015 + 1007 * .I := by
  have h1 : ∀ (k : ℕ), z (2 * k + 1) = ↑(2 * k + 1) + ↑k * Complex.I := by
    intro k
    induction k with
    | zero =>
      norm_num [hz1]
    | succ k ih =>
      have eq1 := hzn (2 * k + 1) (by omega)
      have h10 : z (2 * k + 2) = starRingEnd ℂ (z (2 * k + 1)) + 1 + ↑(2 * k + 1) * Complex.I := by
        simpa using eq1 
      have eq2 := hzn (2 * k + 2) (by omega)
      have h11 : z (2 * k + 3) = starRingEnd ℂ (z (2 * k + 2)) + 1 + ↑(2 * k + 2) * Complex.I := by 
        simpa using eq2 
      rw [show 2 * (k + 1) + 1 = 2 * k + 3 by omega] 
      rw [h11, h10, ih]
      simp [Complex.ext_iff, pow_two, pow_zero, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
      all_goals ring_nf 
      all_goals norm_num 
      all_goals ring 
  have h2 := h1 1007
  norm_num at h2 ⊢
  exact h2