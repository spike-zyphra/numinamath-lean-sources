import Mathlib

theorem algebra_9417 (x : ℝ) : 0 < (x - 2) * (3 - x) ↔ 2 < x ∧ x < 3 := by
  constructor
  · -- Forward direction: If 0 < (x-2)(3-x), then 2 < x ∧ x < 3
    intro h
    cases (mul_pos_iff.mp h) with
    | inl h1 =>
      constructor
      · linarith
      · linarith
    | inr h2 =>
      exfalso
      linarith
  · -- Reverse direction: If 2 < x ∧ x < 3, then 0 < (x-2)(3-x)
    rintro ⟨h1, h2⟩
    apply mul_pos
    all_goals linarith