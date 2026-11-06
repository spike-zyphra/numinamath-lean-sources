import Mathlib

theorem number_theory_209990 (a b c d : ℕ) (h₀ : a + b + c + d = 13)
    (h₁ : ∃ k : ℤ, (2*a+3*b+4*c+5*d)/(13 : ℝ) = k) :
    a ≤ 2 ∨ b ≤ 2 ∨ c ≤ 2 ∨ d ≤ 2 := by 
  rcases h₁ with ⟨k, hk⟩
  have h2 : (2*a+3*b+4*c+5*d : ℝ) = (13 : ℝ) * (k : ℝ) := by
    field_simp at hk
    linarith
  have h3 : (2*a+3*b+4*c+5*d : ℤ) = 13 * k := by 
    exact_mod_cast h2

  by_contra h 
  push_neg at h
  have ha1 : a ≥ 3 := by omega
  have hb1 : b ≥ 3 := by omega
  have hc1 : c ≥ 3 := by omega
  have hd1 : d ≥ 3 := by omega
  omega