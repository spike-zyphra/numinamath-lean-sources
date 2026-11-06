import Mathlib

theorem algebra_314310 (k : ℝ) :
    (∀ x y : ℝ, ((x + 2)^2 / 9 + (y - 2)^2 / 16 = 1) → (x + y - k < 0)) ↔
    k > 5 := by
  constructor
  · -- First, we prove the forward direction: if the implication holds, then k > 5
    intro h
    have h1 := h (-1/5) (26/5) (by norm_num)
    norm_num at h1
    linarith
  · -- Now, we prove the reverse direction: if k > 5, then the implication holds
    intro hk x y h_eq
    have h1 : (x + y) ≤ 5 := by
      nlinarith [sq_nonneg ((x + 2)/3 - 3/5), sq_nonneg ((y - 2)/4 - 4/5),
        sq_nonneg ((x + 2)/3 + 3/5), sq_nonneg ((y - 2)/4 + 4/5),
        h_eq]
    nlinarith