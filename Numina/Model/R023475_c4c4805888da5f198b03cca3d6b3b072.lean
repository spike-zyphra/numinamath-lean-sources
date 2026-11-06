import Mathlib

theorem algebra_308671 (f : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 + 2 * x + 1)
    (m : ℝ) (hm : 0 < m) (t : ℝ) (ht : ∀ x ∈ Set.Icc 1 m, f (x + t) ≤ x) :
    m ≤ 4 := by

  by_contra h
  push_neg at h

  have h1 := ht 1 (by
    constructor <;> linarith
  )
  rw [hf] at h1
  have h1' : (1 + t) ^ 2 + 2 * (1 + t) + 1 ≤ (1 : ℝ) := by
    linarith [h1]

  have h2' : (t + 2) ^ 2 ≤ 1 := by
    nlinarith

  have ht1 : -3 ≤ t := by
    nlinarith [h2']

  have ht2 : t ≤ -1 := by
    nlinarith [h2']

  have h4in : (4 : ℝ) ∈ Set.Icc (1 : ℝ) m := by
    constructor
    · norm_num
    · nlinarith

  have h4 := ht 4 h4in
  rw [hf] at h4
  have h4' : (4 + t) ^ 2 + 2 * (4 + t) + 1 ≤ (4 : ℝ) := by
    linarith [h4]

  have h5 : t ^ 2 + 10 * t + 21 ≤ (0 : ℝ) := by
    nlinarith

  have ht3 : t = -3 := by
    nlinarith

  have hm1 := ht m (by
    constructor <;> linarith
  )
  rw [hf] at hm1
  rw [ht3] at hm1

  nlinarith [sq_nonneg (m - 2), sq_nonneg (m - 4)]