import Mathlib

/- The length of one leg of a right triangle is 9 meters. The lengths of the other two sides are consecutive integer numbers of meters. What is the number of meters in the perimeter of the triangle? -/
theorem algebra_21638 (a b c : ℕ) (h₀ : a^2 + b^2 = c^2) (h₁ : a = 9)
    (h₂ : ∃ n, b = n ∧ c = n + 1) :
    a + b + c = 90 := by 
  obtain ⟨n, hn⟩ := h₂
  subst_vars
  ring_nf
  nlinarith