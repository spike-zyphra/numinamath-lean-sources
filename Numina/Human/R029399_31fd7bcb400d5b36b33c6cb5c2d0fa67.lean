import Mathlib
open Real Set
open scoped BigOperators
theorem algebra_196873 :
  IsLeast {f | ∃ x : Fin 5 → ℝ, (∀ i, 0 ≤ x i) ∧
    -2 * x 0 + x 1 + x 2 = 2 ∧
    x 0 - 2 * x 1 + x 3 = 2 ∧
    x 0 + x 1 + x 4 = 5 ∧
    f = x 1 - x 0} (-3) := by
  -- We need to prove two things: 1. -3 is achievable (so -3 ∈ the set) 2. No smaller value is possible
  constructor
  · -- Let's start with the first part: showing that -3 is achievable
    use λ i => 
      match i with
      | 0 => (4 : ℝ)
      | 1 => (1 : ℝ)
      | 2 => (9 : ℝ)
      | 3 => (0 : ℝ)
      | 4 => (0 : ℝ)
    -- Verify all conditions are satisfied:
    constructor
    -- 1. All values are non-negative
    · intro i
      fin_cases i <;> norm_num 
    constructor
    -- 2. -2 * 4 + 1 + 9 = -8 + 1 + 9 = 2 ✓
    · norm_num 
    constructor
    -- 3. 4 - 2 * 1 + 0 = 4 - 2 + 0 = 2 ✓
    · norm_num 
    constructor
    -- 4. 4 + 1 + 0 = 5 ✓
    · norm_num 
    -- 5. f = 1 - 4 = -3 ✓
    · norm_num 
  · -- Now for the second part - proving that -3 is the minimum value
    intro f h
    rcases h with ⟨x, hx, h₁, h₂, h₃, h₄⟩
    -- use the linarith tactic to show the simplied inequality
    have h₅ : x 1 - x 0 ≥ -3 := by 
      linarith [hx 0, hx 1, hx 2, hx 3, hx 4, h₁, h₂, h₃]
    -- use h4 and h5 to finish the proof
    linarith [h₄, h₅]