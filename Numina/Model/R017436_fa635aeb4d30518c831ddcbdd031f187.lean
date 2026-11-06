import Mathlib

open Real

theorem inequalities_218799 (α β : ℝ) (h₀ : 0 < α) (h₁ : 0 < β)
    (a b : ℝ) (ha : a ∈ Set.Icc α β) (hb : b ∈ Set.Icc α β) :
    a / b + b / a ≤ β / α + α / β ∧
    (a / b + b / a = β / α + α / β ↔ a = α ∧ b = β ∨ a = β ∧ b = α) := by

  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩

  constructor
  · -- Prove the inequality
    have h2 : 0 < a := by linarith 
    have h3 : 0 < b := by linarith 
    have h4 : 0 < a * b := mul_pos h2 h3 
    have h5 : 0 < α * β := mul_pos h₀ h₁ 
    have h6 : a / b + b / a - (β / α + α / β) ≤ 0 := by
      have pos1 : 0 < a * b * (α * β) := by positivity 
      have h7 : a / b + b / a - (β / α + α / β) = 
        ( (a^2 * α * β + b^2 * α * β - a * b * (β^2 + α^2) ) / ( a * b * α * β ) ) := by
        field_simp 
        ring
      rw [h7] at *
      apply div_nonpos_of_nonpos_of_nonneg 
      · -- Show numerator is ≤0 
        nlinarith [ sq_nonneg (a - b), sq_nonneg (a - α), sq_nonneg (a - β), sq_nonneg (b - α), sq_nonneg (b - β), 
          sq_nonneg (a * b - α * β), sq_nonneg (a - b), 
          mul_nonneg (show 0 ≤ a - α by linarith) (show 0 ≤ β - a by linarith), 
          mul_nonneg (show 0 ≤ b - α by linarith) (show 0 ≤ β - b by linarith), 
          mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith), 
          mul_nonneg (show 0 ≤ α by linarith) (show 0 ≤ β by linarith) 
        ]
      · -- Show denominator is ≥0 
        positivity 
    linarith
  · -- Prove the equality holds if and only if $a=\alpha, b=\beta$ or $a=\beta, b=\alpha$
    constructor
    · -- Forward: if equality holds, then ... 
      intro heq 
      have h2 : 0 < a := by linarith 
      have h3 : 0 < b := by linarith 
      have h4 : 0 < a * b := mul_pos h2 h3 
      have h5 : 0 < α * β := mul_pos h₀ h₁ 
      have h7 : a / b + b / a - (β / α + α / β) = 0 := by
        linarith [ heq ]
      have pos1 : 0 < a * b * (α * β) := by positivity 
      have h8 : a^2 * α * β + b^2 * α * β - a * b * (β^2 + α^2) = 0 := by
        have h9 : a / b + b / a - (β / α + α / β) = ( ( a^2 * α * β + b^2 * α * β - a * b * (β^2 + α^2) ) / ( a * b * α * β  ) ) := by
          field_simp 
          ring
        rw [h9] at h7 
        field_simp at h7 
        nlinarith
      have h9 : (a * β - b * α) * (a * α - b * β) = 0 := by nlinarith 
      cases' (mul_eq_zero.mp h9) with h10 h11 
      · -- Case a * β - b * α = 0 
        -- a * β = b * α 
        -- a * b * \beta^2 + something
        -- need to solve the system for equality
        -- We need both factors to be zero
        have h12 : a * β = b * α := by linarith
        have h13 : (a - α) * (a - β) = 0 := by
          nlinarith [ sq_nonneg (a - b), sq_nonneg (a - α), sq_nonneg (a - β), sq_nonneg (b - α), sq_nonneg (b - β) ]
        cases' (mul_eq_zero.mp h13) with h14 h15 
        · -- Case a - α = 0 
          have ha_eq : a = α := by linarith 
          have hb_eq : b = β := by 
            nlinarith 
          left 
          exact ⟨ha_eq, hb_eq⟩ 
        · -- Case a - β = 0 
          have ha_eq : a = β := by linarith 
          have hb_eq : b = α := by 
            nlinarith 
          right 
          exact ⟨ha_eq, hb_eq⟩ 
      · -- Case a * α - b * β = 0 
        -- a * α = b * β 
        have h16 : a * α = b * β := by linarith 
        have h17 : (a - β) * (a - α) = 0 := by
          nlinarith [ sq_nonneg (a - b), sq_nonneg (a - α), sq_nonneg (a - β), sq_nonneg (b - α), sq_nonneg (b - β) ]
        cases' (mul_eq_zero.mp h17) with h18 h19 
        · -- Case a - β = 0 
          have ha_eq : a = β := by linarith 
          have hb_eq : b = α := by 
            nlinarith 
          right 
          exact ⟨ha_eq, hb_eq⟩ 
        · -- Case a - α = 0 
          have ha_eq : a = α := by linarith 
          have hb_eq : b = β := by 
            nlinarith 
          left 
          exact ⟨ha_eq, hb_eq⟩ 
    · -- Backward: if ... then equality holds
      rintro (h | h)
      · -- Case a = α ∧ b = β 
        rcases h with ⟨rfl, rfl⟩ 
        field_simp 
        <;> nlinarith 
      · -- Case a = β ∧ b = α 
        rcases h with ⟨rfl, rfl⟩ 
        field_simp 
        <;> nlinarith