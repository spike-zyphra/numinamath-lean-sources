import Mathlib

theorem algebra_216579 (x : ℝ) (hx : x > 0) :
    (2 * (2 * x + 6 * x + 2 * 6)) * (4 * (2 + 6 + x)) ≤ 88 * (2 * 6 * x) ↔
    3 ≤ x ∧ x ≤ 4 := by
  constructor
  · -- Forward direction: Assume the inequality holds, prove 3 ≤ x ∧ x ≤ 4
    intro h
    have h1 : (2 * (2 * x + 6 * x + 2 * 6)) * (4 * (2 + 6 + x)) = (16 * x + 24) * (32 + 4 * x) := by
      ring_nf
    have h2 : 88 * (2 * 6 * x) = 1056 * x := by
      ring_nf
    rw [h1, h2] at h
    have h3 : 64 * x^2 - 448 * x + 768 ≤ 0 := by
      nlinarith
    have h4 : x^2 - 7 * x + 12 ≤ 0 := by
      nlinarith
    have h5 : (x - 3) * (x - 4) ≤ 0 := by
      nlinarith
    constructor
    · -- Prove 3 ≤ x
      nlinarith
    · -- Prove x ≤ 4
      nlinarith
  · -- Backward direction: Assume 3 ≤ x ∧ x ≤ 4, prove the inequality
    rintro ⟨h3, h4⟩
    have h1 : (2 * (2 * x + 6 * x + 2 * 6)) * (4 * (2 + 6 + x)) = (16 * x + 24) * (32 + 4 * x) := by
      ring_nf
    have h2 : 88 * (2 * 6 * x) = 1056 * x := by
      ring_nf
    rw [h1, h2]
    have h5 : (x - 3) * (x - 4) ≤ 0 := by
      nlinarith
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 4)]