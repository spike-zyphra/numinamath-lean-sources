import Mathlib

/- Evaluate $2011 \times 20122012 \times 201320132013-2013 \times 20112011 \times 201220122012$. -/
theorem algebra_608830 :
  (2011 * 20122012 * 201320132013 - 2013 * 20112011 * 201220122012 : ℤ) = 0 := by
  -- First, we rewrite the expression in a more manageable form
  have h₁ : (20122012 : ℤ) = 2012 * 10001 := by norm_num
  have h₂ : (201320132013 : ℤ) = 2013 * 100010001 := by norm_num
  have h₃ : (20112011 : ℤ) = 2011 * 10001 := by norm_num
  have h₄ : (201220122012 : ℤ) = 2012 * 100010001 := by norm_num
  rw [h₁, h₂, h₃, h₄]
  clear * -
  -- Now it follows from commutativity and associativity of multiplication
  generalize (2011 : ℤ) = a
  generalize (2012 : ℤ) = b
  generalize (2013 : ℤ) = c
  generalize (10001 : ℤ) = d
  generalize (100010001 : ℤ) = e
  ring
