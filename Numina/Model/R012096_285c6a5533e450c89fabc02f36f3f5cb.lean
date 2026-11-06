import Mathlib

theorem number_theory_78279 (a b c S : ℚ) (h₀ : a > 0) (h₁ : b > 0) (h₂ : c > 0)
    (h₃ : a^2 + b^2 = c^2) (h₄ : S = (1/2) * a * b) :
    ∃ a' b' c' : ℚ, a' > 0 ∧ b' > 0 ∧ c' > 0 ∧ a'^2 + b'^2 = c'^2 ∧ S = (1/2) * a' * b' ∧ ({a, b, c} : Finset ℚ) = {a', b', c'} := by 
  use b, a, c
  constructor
  · -- Show b > 0
    exact h₁
  constructor
  · -- Show a > 0 
    exact h₀ 
  constructor
  · -- Show c > 0 
    exact h₂
  constructor
  · -- Show b ^ 2 + a ^ 2 = c ^ 2 
    have eq : b^2 + a^2 = c^2 := by
      nlinarith
    nlinarith 
  constructor
  · -- Show S = (1 / 2) * b * a 
    rw [h₄]
    ring 
  · -- Show {a, b, c} = {b, a, c} 
    ext x 
    simp [Finset.mem_insert, Finset.mem_singleton] 
    <;> tauto