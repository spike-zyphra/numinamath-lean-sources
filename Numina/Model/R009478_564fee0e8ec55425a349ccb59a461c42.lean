import Mathlib

theorem algebra_9143 :
    (∀ x : ℝ, (x - 2) * (x - 4) < 0 → x > 0) ∧ ¬ (∀ x : ℝ, x > 0 → (x - 2) * (x - 4) < 0) := by
  constructor
  · -- Proof that x > 0 is a necessary condition
    intro x h
    have h1 : (x - 2) * (x - 4) < 0 := h
    cases mul_neg_iff.mp h1 with
    | inl h2 =>
      linarith
    | inr h2 =>
      linarith
  · -- Proof that x > 0 is not a sufficient condition
    intro h
    have h1 := h 1 (by norm_num)
    norm_num at h1
    all_goals norm_num at h1 ⊢
    all_goals linarith