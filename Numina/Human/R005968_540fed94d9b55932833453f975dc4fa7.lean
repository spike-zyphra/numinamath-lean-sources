import Mathlib

/-Solve x=√(x-1/x) + √(1-1/x) for x-/
theorem algebra_610931 {x: ℝ} (hx: 1 ≤ x) (h: x = √(x-1/x) + √(1-1/x)): x = (1 + √5) / 2 := by

 -- we first show some fundamental facts --
  have ineq1: 0 ≤ x - 1/x:= by
    rw [show x - 1/x = (x ^ 2 - 1) / x by field_simp;ring]
    apply div_nonneg
    nlinarith
    linarith
  have ineq2: 0 ≤ 1 - 1/x := by
    rw [show 1 - 1/x = (x - 1) / x by field_simp]
    apply div_nonneg
    nlinarith
    linarith
  have eq1: (√(x-1/x)) ^ 2 = x - 1/x := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    exact ineq1
    apply Real.sqrt_nonneg
  have eq2: (√(1-1/x)) ^ 2 = 1 - 1/x := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    exact ineq2
    apply Real.sqrt_nonneg

  -- now we prove by direct computation --
  replace h: x ^ 2 = (√(x-1/x) + √(1-1/x)) ^ 2 := by
     nth_rewrite 1 [h]
     rfl
  have eq: (√(x-1/x) + √(1-1/x)) ^ 2 = x - 2 / x + 1 + 2 * √(x-1/x) * √(1-1/x) := by
    ring_nf
    rw [show x⁻¹ = 1/x by field_simp]
    rw [eq1,eq2]
    ring
  rw [eq] at h
  clear eq
  replace h: x ^ 2 - x - 1 + 2 / x = 2 * √(x-1/x) * √(1-1/x) := by
    nth_rewrite 1 [h]
    ring
  replace h: (x ^ 2 - x - 1 + 2 / x) ^ 2 = (2 * √(x-1/x) * √(1-1/x)) ^ 2 := by
    rw [h]
  have eq: (2 * √(x-1/x) * √(1-1/x)) ^ 2 = 4 * (x-1/x) * (1-1/x) := by
    ring_nf
    rw [show x⁻¹ = 1/x by field_simp]
    rw [eq1,eq2]
    ring
  rw [eq] at h
  clear eq
  replace h: x ^ 2 * (x ^ 2 - x - 1 + 2 / x) ^ 2 = x ^ 2 * 4 * (x-1/x) * (1-1/x) := by
    nth_rewrite 1 [h]
    ring
  replace h: x ^ 2 * (x ^ 2 - x - 1 + 2 / x) ^ 2 - x ^ 2 * 4 * (x-1/x) * (1-1/x) = 0 := by
    nth_rewrite 1 [h]
    ring
  have eq: x ^ 2 * (x ^ 2 - x - 1 + 2 / x) ^ 2 - x ^ 2 * 4 * (x-1/x) * (1-1/x)
  = x ^ 2 * (x ^ 2 - x - 1) ^ 2 := by  -- factorization- -
    field_simp
    ring
  rw [eq] at h
  clear eq eq1 eq2 ineq1 ineq2
  simp at h
  have ne: x ≠ 0 := by linarith
  simp [ne] at h
  have fac: x ^ 2 - x - 1 = (x - (1 + √5) / 2) * (x - (1 - √5) / 2) := by
    ring_nf
    have eq: (√5)^2 = 5 := by
      symm
      rw [← Real.sqrt_eq_iff_eq_sq]
      norm_num
      apply Real.sqrt_nonneg
    rw [eq]
    ring
  rw [fac] at h
  clear fac
  simp at h
  rcases h with h | h
  . nlinarith
  . replace h: x = (1 - √5) / 2 := by
      nlinarith
    rw [h] at hx
    absurd hx
    simp
    have o: 0 ≤ √5 := by
      apply Real.sqrt_nonneg
    nlinarith [o]