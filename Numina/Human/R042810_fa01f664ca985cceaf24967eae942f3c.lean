import Mathlib

/- 4. 4.1. For the quadratic trinomial \( f(x) = a x^{2} + b x + c \), where \( a > 0 \), the condition \( |f(1)| = |f(2)| = |f(3)| = 1 \) is satisfied. What can the coefficients be? -/
theorem algebra_108757 {a b c : ℝ} (ha : a > 0) (h1 : |a + b + c| = 1) (h2 : |4*a + 2*b + c| = 1)
    (h3 : |9*a + 3*b + c| = 1) :
    (a = 2 ∧ b = -8 ∧ c = 7) ∨ (a = 1 ∧ b = -3 ∧ c = 1) ∨ (a = 1 ∧ b = -5 ∧ c = 5) := by 
  cases' abs_cases (a + b + c) with h₀ h₀ <;> cases' abs_cases (4*a + 2*b + c) with h₁ h₁ <;> cases' abs_cases (9*a + 3*b + c) with h₂ h₂ <;> simp_all
  <;> try {linarith} <;> try { exact Or.inl ⟨by linarith, by linarith, by linarith⟩ }
  <;> try { exact Or.inr (Or.inl ⟨by linarith, by linarith, by linarith⟩) }
  <;> try { exact Or.inr (Or.inr ⟨by linarith, by linarith, by linarith⟩) }