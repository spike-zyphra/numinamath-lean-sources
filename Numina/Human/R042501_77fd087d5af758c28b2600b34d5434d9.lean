import Mathlib
open Real Set

/- Determine the maximum value of the function $y=3-2\cos \left( x+ \frac{\pi}{4} \right)$ and the value of $x$ when the maximum occurs. $ -/
theorem algebra_9452 {f : ℝ → ℝ} (hf : f = λ x => 3 - 2 * cos (x + π / 4)) :
    IsGreatest (range f) 5 ∧
    ∀ x, f x = 5 ↔ ∃ k : ℤ, x = 2 * k * π + 3 * π / 4 := by

  -- Expand the definitions and split the goals
  simp [IsGreatest, upperBounds, hf]
  refine ⟨⟨?_, ?_⟩, ?_⟩

  . -- 5 can be achieved by setting x = 3π/4
    use 3 * π / 4
    ring_nf
    linarith [cos_pi]

  . -- 5 is un upper bound because cos _ ≥ -1
    intro x
    linarith [neg_one_le_cos (x + π / 4)]

  . intro x
    -- Rewrite the equation as cos (x + π / 4) = -1
    have h : 3 - 2 * cos (x + π / 4) = 5 ↔ cos (x + π / 4) = -1 := by constructor <;> intro h <;> linarith
    rw [h, cos_eq_neg_one_iff]

    -- We need to prove (∃ k, π + ↑k * (2 * π) = x + π / 4) ↔ (∃ k, x = 2 * ↑k * π + 3 * π / 4)
    -- It holds because the predicates are equivalent pointwise
    apply Eq.to_iff; congr; ext k
    constructor <;> intro h <;> linarith
