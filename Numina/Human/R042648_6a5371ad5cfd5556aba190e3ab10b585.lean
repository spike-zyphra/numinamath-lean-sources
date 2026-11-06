import Mathlib

/- What is the smallest positive integer $n$ for which $(12{,}500{,}000)\cdot n$ leaves a remainder of $111$ when divided by $999{,}999{,}999$? -/
theorem number_theory_22966 :
    IsLeast {n : ℕ | 0 < n ∧ (12500000 * n) % 999999999 = 111} 8880 := by 
  exact ⟨by decide, fun n ⟨h₁, h₂⟩ => by omega⟩