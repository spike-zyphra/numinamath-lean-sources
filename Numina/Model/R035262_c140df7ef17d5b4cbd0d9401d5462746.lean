import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_181364 (f : ℝ → ℝ) (hf : f = λ x => x^4 - 6 * x^2 + 1) :
    IsGreatest {y | ∃ x ∈ Icc (-1) 3, deriv f x = y} 72 ∧
    IsLeast {y | ∃ x ∈ Icc (-1) 3, deriv f x = y} (-8) := by

  have hf' : ∀ x, deriv f x = 4 * x^3 - 12 * x := by
    intro x
    rw [hf]
    simp [deriv_pow, deriv_const, mul_comm]
    all_goals field_simp <;> ring

  constructor
  · -- Prove that 72 is greatest in derivative image
    constructor
    · -- Prove that exists x in Icc (-1) 3 such that deriv f x = 72
      use 3
      constructor
      · -- Show that 3 ∈ Icc (-1) 3
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that deriv f 3 = 72
        rw [hf']
        norm_num
    · -- Prove that for any y in the set, y ≤ 72
      intro y hy
      rcases hy with ⟨x, hx, h_eq⟩
      rw [hf'] at h_eq
      rcases hx with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2 - 3),
        sq_nonneg (x * (x - 3)), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((x - 2) * (x - 2)), mul_nonneg (show (0 : ℝ) ≤ 3 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]
  · -- Prove that -8 is least in derivative image
    constructor
    · -- Prove that exists x in Icc (-1) 3 such that deriv f x = -8
      use 1
      constructor
      · -- Show that 1 ∈ Icc (-1) 3
        exact ⟨by norm_num, by norm_num⟩
      · -- Show that deriv f 1 = -8
        rw [hf']
        norm_num
    · -- Prove that for any y in the set, -8 ≤ y
      intro y hy
      rcases hy with ⟨x, hx, h_eq⟩
      rw [hf'] at h_eq
      rcases hx with ⟨hx1, hx2⟩
      nlinarith [sq_nonneg (x - 3), sq_nonneg (x + 1), sq_nonneg (x - 1), sq_nonneg (x^2 - 3),
        sq_nonneg (x * (x - 3)), sq_nonneg ((x - 1) * (x + 1)), sq_nonneg ((x - 2) * (x - 2)), mul_nonneg (show (0 : ℝ) ≤ 3 - x by linarith) (show (0 : ℝ) ≤ x + 1 by linarith)]