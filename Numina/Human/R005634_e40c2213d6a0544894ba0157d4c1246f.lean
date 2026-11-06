import Mathlib

open Real

/-Pick a subset of at least four of the following seven numbers, order them from least to greatest,
and write down their labels (corresponding letters from A through G) in that order:
(A) π;
(B) √2 + √3
(C) √10
​(D) 355/113
(E) 16tan⁻¹(1/5) - 4tan⁻¹(1/240)
(F)ln(23); and
(G) 2^√e.-/

theorem number_theory_609191:
  π < 355 / 113 ∧ 355 / 113 < √2 + √3 ∧ √2 + √3 < √10 := by

  refine ⟨?_, ?_, ?_⟩
  .
    have l:= Real.pi_lt_d20
    suffices 3.14159265358979323847 < (355: ℝ) / 113 by
      linarith
    norm_num

  .
    rw [show (355: ℝ) / 113 = |355 / 113| by symm; apply abs_of_nonneg; norm_num]
    apply abs_lt_of_sq_lt_sq
    ring_nf
    have f1: √2 ^ 2 = 2 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    have f2: √3 ^ 2 = 3 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    have n1: 0 ≤ √2 := by
      apply Real.sqrt_nonneg
    have n2: 0 ≤ √3 := by
      apply Real.sqrt_nonneg
    rw [f1, f2]
    suffices 126025 / 12769 - 5 < √2 * √3 * 2 by
      linarith
    norm_num
    rw [show (62180: ℝ) / 12769 = |62180 / 12769| by symm; apply abs_of_nonneg; norm_num]
    apply abs_lt_of_sq_lt_sq
    ring_nf
    rw [f1, f2]
    norm_num
    nlinarith
    suffices 0 ≤ √2 ∧ 0 ≤ √3 by linarith
    refine ⟨(by apply Real.sqrt_nonneg), (by apply Real.sqrt_nonneg)⟩

  .
    have o: 0 ≤ √2 + √3 := by
      suffices 0 ≤ √2 ∧ 0 ≤ √3 by linarith
      refine ⟨(by apply Real.sqrt_nonneg), (by apply Real.sqrt_nonneg)⟩
    rw [show √2 + √3 = |√2 + √3| by symm; apply abs_of_nonneg; tauto]
    apply abs_lt_of_sq_lt_sq
    ring_nf
    have f1: √2 ^ 2 = 2 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    have f2: √3 ^ 2 = 3 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    have f3: √10 ^ 2 = 10 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    rw [f1, f2, f3]
    suffices √2 * √3 * 2 < 5 by linarith
    have n1: 0 ≤ √2 := by
      apply Real.sqrt_nonneg
    have n2: 0 ≤ √3 := by
      apply Real.sqrt_nonneg
    rw [show √2 * √3 * 2 = |√2 * √3 * 2| by symm; apply abs_of_nonneg; nlinarith]
    apply abs_lt_of_sq_lt_sq
    ring_nf
    rw [f1, f2]
    norm_num
    norm_num
    apply Real.sqrt_nonneg
    