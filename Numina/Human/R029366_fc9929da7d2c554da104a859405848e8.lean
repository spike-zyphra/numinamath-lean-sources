import Mathlib

/- Four distinct integers $a$, $b$, $c$ and $d$ have the property that when added in pairs, the sums 16, 19, 20, 21, 22, and 25 are obtained. What are the four integers in increasing order? (place a comma and then a space between each integer) -/
theorem algebra_21394 {a b c d : ℤ} (h₀ : a < b) (h₁ : b < c) (h₂ : c < d)
    (h₃ : a + b = 16) (h₄ : a + c = 19) (h₅ : a + d = 20) (h₆ : b + c = 21)
    (h₇ : b + d = 22) (h₈ : c + d = 25) :
    a = 7 ∧ b = 9 ∧ c = 12 ∧ d = 13 := by 
  refine' ⟨_, _, _, _⟩
  all_goals omega