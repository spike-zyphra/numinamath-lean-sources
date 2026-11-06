import Mathlib

/- ## Task 1.

Determine all pairs $(a, b)$ of real numbers for which


$$

a+\frac{a+8 b}{a^{2}+b^{2}}=2 \quad \text { and } \quad b+\frac{8 a-b}{a^{2}+b^{2}}=0

$$
 -/
theorem algebra_252844 (a b : ℝ) :
    a^2 + b^2 ≠ 0 ∧ a + (a + 8 * b) / (a ^ 2 + b ^ 2) = 2 ∧
    b + (8 * a - b) / (a ^ 2 + b ^ 2) = 0 ↔
    (a = -1 ∧ b = 2) ∨ (a = 3 ∧ b = -2) := by
  constructor
  -- left to right direction
  . rintro ⟨hsq_nz, h₁, h₂⟩
    -- h1 * b + h2 * a gives us 2ab + 8 = 2b
    have h₃ : 2 * a * b +  8 * (a^2 + b^2) / (a^2 + b^2) = 2 * b := by linear_combination h₁ * b + h₂ * a
    field_simp at h₃
    -- h1 * a - h2 * b gives us a^2 - b^2 + 1 = 2a, which is equivlaent to b^2 = (a-1)^2
    have h₄ : a^2 - b^2 + (a^2 + b^2) / (a^2 + b^2) = 2 * a := by linear_combination h₁ * a - h₂ * b
    field_simp at h₄
    -- so b = a-1 or b = -(a-1)
    replace h₄ : b^2 = (a-1)^2 := by linarith
    obtain rfl | rfl := eq_or_eq_neg_of_sq_eq_sq b (a-1) h₄
      -- first case gives us (a-1)^2 = -4 in h3, but that is impossible
    . replace h₃ : (a-1)^2 = -4 := by linarith only [h₃]
      have : 0 ≤ (a-1)^2 := by positivity
      linarith
      -- second case gives us (a-1)^2 = 4 in h3, that means a-1 = 2 or a-1 = -2
    . replace h₃ : (a-1)^2 = 2^2 := by linarith only [h₃]
      obtain h | h := eq_or_eq_neg_of_sq_eq_sq (a-1) 2 h₃
      -- the two case give us the two set of equation (using algebraic manipulation)
      . right
        exact ⟨by linarith, by linarith⟩
      . left
        exact ⟨by linarith, by linarith⟩
  -- right to left direction, just replace and calculate
  . rintro h
    obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h
    all_goals norm_num