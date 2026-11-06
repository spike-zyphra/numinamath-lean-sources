import Mathlib

open Real

theorem algebra_16311 (x : ℝ) (hx : 0 ≤ 4 * x - 3) :
    sqrt (4 * x - 3) + 10 / sqrt (4 * x - 3) = 7 ↔ x = 7 / 4 ∨ x = 7 := by
  constructor
  · -- Assume $\sqrt{4x-3}+\frac{10}{\sqrt{4x-3}}=7$, prove $x = 7 / 4 ∨ x = 7$
    intro h
    let u := sqrt (4 * x - 3)
    have u_eq : u = sqrt (4 * x - 3) := rfl
    rw [←u_eq] at h
    have uneq : u ≠ 0 := by 
      unfold u
      by_contra h2
      have h3 : sqrt (4 * x - 3) = 0 := by linarith [Real.sqrt_nonneg (4 * x - 3)]
      have h4 : 4 * x - 3 = 0 := by
        rw [Real.sqrt_eq_zero (by linarith)] at h3
        linarith
      have h5 : sqrt (4 * x - 3) = 0 := by linarith [Real.sqrt_nonneg (4 * x - 3)]
      have h6 : 10 / sqrt (4 * x - 3) = 0 := by
        rw [h5]
        norm_num
      rw [u_eq] at h
      linarith
    have ueq_aux : u ^ 2 - 7 * u + 10 = 0 := by 
      rw [←h]
      field_simp
      ring_nf
    have decom : (u - 2) * (u - 5) = 0 := by
      rw [←ueq_aux]
      ring
    have : u = 2 ∨ u = 5 := Or.imp (fun h => by linarith [sqrt_nonneg (4 * x - 3)]) (fun h => by linarith [sqrt_nonneg (4 * x - 3)]) (eq_zero_or_eq_zero_of_mul_eq_zero decom)
    obtain h1 | h2 := this
    left 
    unfold u at h1
    have h4 : (sqrt (4 * x - 3)) ^ 2 = 4 * x - 3 := by
      rw [Real.sq_sqrt]
      linarith
    rw [h1] at h4
    linarith
    right
    have h4 : (sqrt (4 * x - 3)) ^ 2 = 4 * x - 3 := by
      rw [Real.sq_sqrt]
      linarith
    unfold u at h2
    rw [h2] at h4
    linarith
  · -- Prove that if $x = 7/4$ or $x = 7$, then $\sqrt{4x-3}+\frac{10}{\sqrt{4x-3}}=7$
    
    intro h
    cases' h with h1 h2
    · -- Case $x = 7/4$
      have h3 : 4 * x - 3 = 4 := by
        rw [h1]
        norm_num
      have h4 : sqrt (4 * x - 3) = 2 := by
        rw [h3]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      rw [h4]
      norm_num
    · -- Case $x = 7$
      have h3 : 4 * x - 3 = 25 := by
        rw [h2]
        norm_num
      have h4 : sqrt (4 * x - 3) = 5 := by
        rw [h3]
        rw [Real.sqrt_eq_iff_eq_sq] <;> norm_num
      rw [h4]
      norm_num
    