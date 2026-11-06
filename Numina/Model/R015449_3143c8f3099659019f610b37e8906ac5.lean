import Mathlib

theorem algebra_221823 (a b c : ℝ) (f : ℝ → ℝ) (hf : ∀ x, |x| ≤ 1 → |f x| ≤ 1)
    (h : f = fun x => a * x ^ 2 + b * x + c) : |a| ≤ 2 := by
  have h1 := hf 0 (by norm_num)
  simp [h] at h1
  have h2 := hf 1 (by norm_num)
  simp [h] at h2
  have h3 := hf (-1) (by norm_num)
  simp [h] at h3
  have h4 := hf (1 / 2) (by
    norm_num [abs_le]
  )
  simp [h] at h4
  have h5 := hf (-1 / 2) (by
    norm_num [abs_le]
  )
  simp [h] at h5
  have h11 : -1 ≤ c ∧ c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h1]
    · linarith [abs_le.mp h1]
  have h21 : -1 ≤ a + b + c ∧ a + b + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h2]
    · linarith [abs_le.mp h2]
  have h31 : -1 ≤ a - b + c ∧ a - b + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h3]
    · linarith [abs_le.mp h3]
  have h41 : -1 ≤ a * (1 / 2) ^ 2 + b * (1 / 2) + c ∧ a * (1 / 2) ^ 2 + b * (1 / 2) + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h4]
    · linarith [abs_le.mp h4]
  have h51 : -1 ≤ a * (-1 / 2) ^ 2 + b * (-1 / 2) + c ∧ a * (-1 / 2) ^ 2 + b * (-1 / 2) + c ≤ 1 := by
    constructor
    · linarith [abs_le.mp h5]
    · linarith [abs_le.mp h5]
  have h6 : -2 ≤ a := by
    nlinarith
  have h7 : a ≤ 2 := by
    nlinarith
  apply abs_le.mpr
  constructor <;> linarith