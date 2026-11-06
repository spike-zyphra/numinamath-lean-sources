import Mathlib

def A : Set ℝ := {y | ∃ x, y = x ^ 2 - 4 * x + 3}
def B : Set ℝ := {y | ∃ x, y = -x ^ 2 - 2 * x}

theorem algebra_205172 : A ∩ B = {y | -1 ≤ y ∧ y ≤ 1} ∧ A ∪ B = ⊤ := by 
  constructor 
  · -- Prove $A \cap B = \{y \mid -1 \leq y \wedge y \leq 1\}$
    ext y
    simp [A, B]
    constructor
    · -- Assume $y \in A \cap B$
      rintro ⟨⟨x, hx⟩, ⟨z, hz⟩⟩
      constructor
      · -- Show $-1 \leq y$
        have h1 : -1 ≤ y := by
          have h1 : (x - 2) ^ 2 ≥ 0 := by 
            apply sq_nonneg
          linarith [hx]
        linarith
      · -- Show $y \leq 1$
        have h2 : y ≤ 1 := by
          have h2 : (z + 1) ^ 2 ≥ 0 := by 
            apply sq_nonneg
          nlinarith [hz]
        linarith
    · -- Assume $-1 \leq y \wedge y \leq 1$
      rintro ⟨hy1, hy2⟩
      constructor
      · -- Show that $y \in A$
        use 2 + Real.sqrt (1 + y)
        nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y by linarith)]
      · -- Show that $y \in B$
        use -1 + Real.sqrt (1 - y)
        nlinarith [Real.sqrt_nonneg (1 - y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by linarith)]
  · -- Prove $A \cup B = \mathbb{R}$
    ext y
    simp [A, B]
    by_cases h : y ≥ -1
    · -- Case where $y \geq -1$
      left
      use 2 + Real.sqrt (1 + y)
      nlinarith [Real.sqrt_nonneg (1 + y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 + y by linarith)]
    · -- Case where $y < -1$
      right
      use -1 - Real.sqrt (1 - y)
      nlinarith [Real.sqrt_nonneg (1 - y), Real.sq_sqrt (show (0 : ℝ) ≤ 1 - y by nlinarith)]