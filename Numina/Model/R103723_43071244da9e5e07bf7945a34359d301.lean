import Mathlib

open Real Set
open scoped Real

theorem algebra_239978 (a : ℝ) :
  (∃ x : ℝ, sin x ^ 2 + cos x + a = 0) ↔ a ∈ Icc (-5/4) 1 := by 
  constructor
  · -- Forward: if there exists a real solution then $a \in [-\frac{5}{4}, 1]$
    rintro ⟨x, hx⟩
    have h1 : sin x ^ 2 + cos x + a = 0 := hx
    have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq x]
    rw [h2] at h1
    have h3 : 1 - cos x ^ 2 + cos x + a = 0 := by linarith
    have h4 : cos x ^ 2 - cos x - (1 + a) = 0 := by linarith
    have h5 : -1 ≤ cos x := Real.neg_one_le_cos x
    have h6 : cos x ≤ 1 := Real.cos_le_one x
    constructor
    · -- Show that -5/4 ≤ a
      nlinarith [sq_nonneg (cos x - 1/2), sq_nonneg (cos x - 1), sq_nonneg (cos x + 1)]
    · -- Show that a ≤ 1
      nlinarith [sq_nonneg (cos x - 1), sq_nonneg (cos x + 1)]
  · -- Backward: if $a \in [-\frac{5}{4}, 1]$ then there exists a real solution
    rintro ⟨h1, h2⟩
    have h3 : -1 ≤ (1 - Real.sqrt (5 + 4 * a)) / 2 := by
      have h6 : Real.sqrt (5 + 4 * a) ≤ 3 := by
        have h7 : 5 + 4 * a ≤ 9 := by linarith
        have h8 : Real.sqrt (5 + 4 * a) ≤ Real.sqrt (9 : ℝ) := Real.sqrt_le_sqrt (by linarith)
        have h9 : Real.sqrt (9 : ℝ) = 3 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          <;> nlinarith
        linarith
      nlinarith [Real.sqrt_nonneg (5 + 4 * a), Real.sq_sqrt (show (5 + 4 * a) ≥ 0 by linarith)]
    have h4 : (1 - Real.sqrt (5 + 4 * a)) / 2 ≤ 1 := by
      nlinarith [Real.sqrt_nonneg (5 + 4 * a)]
    use Real.arccos ((1 - Real.sqrt (5 + 4 * a)) / 2)
    have hsin2 : sin (Real.arccos ((1 - Real.sqrt (5 + 4 * a)) / 2)) ^ 2 = 1 - cos (Real.arccos ((1 - Real.sqrt (5 + 4 * a)) / 2)) ^ 2 := by 
      rw [Real.sin_sq]
    have hcos : cos (Real.arccos ((1 - Real.sqrt (5 + 4 * a)) / 2)) = (1 - Real.sqrt (5 + 4 * a)) / 2 := by 
      apply Real.cos_arccos
      all_goals 
        nlinarith [Real.sqrt_nonneg (5 + 4 * a), Real.sq_sqrt (show (5 + 4 * a) ≥ 0 by linarith)]
    rw [hsin2, hcos]
    nlinarith [Real.sqrt_nonneg (5 + 4 * a), Real.sq_sqrt (show (5 + 4 * a) ≥ 0 by linarith)]