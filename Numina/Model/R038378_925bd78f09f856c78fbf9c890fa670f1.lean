import Mathlib

theorem algebra_122919 (a : ℕ → ℝ) (ha1 : a 0 = 1) (ha2 : a 1 = 1) (ha3 : a 2 = 2)
    (han : ∀ n, a n * a (n + 1) * a (n + 2) ≠ 1)
    (han' : ∀ n, a n * a (n + 1) * a (n + 2) * a (n + 3) = a n + a (n + 1) + a (n + 2) + a (n + 3)) :
    ∑ i in Finset.range 100, a i = 200 := by

  have a4 : a 3 = 4 := by
    have h1 := han' 0
    simp [ha1, ha2, ha3] at h1
    nlinarith

  have a5 : a 4 = 1 := by
    have h1 := han' 1
    simp [ha2, ha3, a4] at h1
    nlinarith

  have a6 : a 5 = 1 := by
    have h1 := han' 2
    simp [ha3, a4, a5] at h1
    nlinarith

  have a7 : a 6 = 2 := by
    have h1 := han' 3
    simp [a4, a5, a6] at h1
    nlinarith

  have recurrence : ∀ n, a (n + 4) = a n := by
    intro n
    have h1 := han' n
    have h2 := han' (n + 1)
    simp [show n + 1 + 1 = n + 2 by omega, show n + 1 + 2 = n + 3 by omega, show n + 1 + 3 = n + 4 by omega] at h2
    have h3 : a (n) * (a (n + 1) * a (n + 2) * a (n + 3) - 1) = (a (n + 1) + a (n + 2) + a (n + 3)) := by linarith
    have h4 : a (n + 4) * (a (n + 1) * a (n + 2) * a (n + 3) - 1) = (a (n + 1) + a (n + 2) + a (n + 3)) := by linarith
    have h10 : a (n + 1) * a (n + 2) * a (n + 3) - 1 ≠ 0 := by
      by_contra h11
      have h12 : a (n + 1) * a (n + 2) * a (n + 3) = 1 := by linarith
      have h13 : a (n + 1) * a (n + 2) * a (n + 3) ≠ 1 := han (n + 1)
      contradiction

    have h14 : a n = a (n + 4) := by
      apply (mul_left_inj' h10).mp
      linarith

    linarith

  norm_num [Finset.sum_range_succ, ha1, ha2, ha3, a4, a5, a6, a7, recurrence]
  <;> try { tauto }
  <;> try { nlinarith }