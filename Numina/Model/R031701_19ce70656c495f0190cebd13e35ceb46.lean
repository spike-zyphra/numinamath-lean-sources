import Mathlib

theorem number_theory_7528
    (x y : ℝ) :
    ⌊x⌋ + ⌊y⌋ ≤ ⌊x + y⌋ ∧
    ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by 
  constructor
  · -- Proof of $\lfloor x \rfloor + \lfloor y \rfloor \leq \lfloor x + y \rfloor$
    exact Int.le_floor_add x y 
  · -- Proof of $\lfloor x + y \rfloor \leq \lfloor x \rfloor + \lfloor y \rfloor + 1$ 
    have h1 : ⌊x + y⌋ ≤ x + y := by 
      exact Int.floor_le (x + y)
    have h2 : x < ⌊x⌋ + 1 := by 
      exact Int.lt_floor_add_one x 
    have h3 : y < ⌊y⌋ + 1 := by 
      exact Int.lt_floor_add_one y
    have h4 : x + y < (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by 
      linarith 
    have h5 : ⌊x + y⌋ ≤ ⌊x⌋ + ⌊y⌋ + 1 := by 
      by_contra h 
      push_neg at h 
      have h6 : ⌊x + y⌋ ≥ ⌊x⌋ + ⌊y⌋ + 2 := by 
        omega 
      have h7 : (⌊x + y⌋ : ℝ) ≥ (⌊x⌋ + ⌊y⌋ + 2 : ℝ) := by 
        exact_mod_cast h6 
      linarith 
    exact_mod_cast h5