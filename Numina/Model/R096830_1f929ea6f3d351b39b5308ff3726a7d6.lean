import Mathlib

theorem algebra_291484 (a : ℤ) : 0 < (5 + a) * (3 - a) ↔ a ∈ Finset.Icc (-4) 2 := by
  simp only [Finset.mem_Icc]
  constructor
  · -- Forward: If 0 < (5 + a) * (3 - a), then a ∈ [-4, 2]
    intro h
    have h1 : (5 + a) * (3 - a) > 0 := by linarith
    cases mul_pos_iff.mp h1 with
    | inl h2 =>
      -- Case 1: Both factors are positive
      -- 5 + a > 0 and 3 - a > 0
      -- Thus, a > -5 and a < 3
      constructor <;> linarith
    | inr h2 =>
      -- Case 2: Both factors are negative
      -- 5 + a < 0 and 3 - a < 0
      -- Thus, a < -5 and a > 3 (contradiction)
      linarith
  · -- Backward: If a ∈ [-4, 2], then 0 < (5 + a) * (3 - a)
    rintro ⟨h1, h2⟩
    -- a ≥ -4 and a ≤ 2
    -- Then, 5 + a ≥ 1 and 3 - a ≥ 1
    have h3 : 5 + a > 0 := by linarith
    have h4 : 3 - a > 0 := by linarith
    exact mul_pos h3 h4