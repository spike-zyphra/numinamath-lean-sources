import Mathlib

theorem other_240672 (A H : ℝ) (hA : A > 0) (hH : H > 0)
    (h1 : A * 0.88 = H * 0.48) (h2 : H * 0.48 = A * 0.3) :
    A = 0.3 ∧ H = 0.2 := by 
  have h3 : A * (0.88 : ℝ) = A * (0.3 : ℝ) := by 
    linarith [h1, h2]
  have h4 : A * (0.58 : ℝ) = 0 := by
    ring_nf at h3 ⊢
    linarith
  cases (mul_eq_zero.mp h4) with
  | inl h6 =>
    linarith -- contradicts
  | inr h7 =>
    norm_num at h7
    all_goals linarith