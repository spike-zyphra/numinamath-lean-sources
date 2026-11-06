import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_223107 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = (x + a)^2 / ((a - b) * (a - c)) + (x + b)^2 / ((b - a) * (b - c)) + (x + c)^2 / ((c - a) * (c - b))) :
  ∀ x, f x = 1 := by
  intro x
  rw [h₀ x]
  have h1 : a - b ≠ 0 := sub_ne_zero_of_ne ha
  have h2 : b - a ≠ 0 := by 
    intro h
    apply ha
    linarith
  have h3 : b - c ≠ 0 := sub_ne_zero_of_ne hb
  have h4 : c - b ≠ 0 := by
    intro h
    apply hb
    linarith
  have h5 : a - c ≠ 0 := by 
    intro h
    apply hc
    linarith
  have h6 : c - a ≠ 0 := by 
    intro h
    apply hc
    linarith
  -- These non-zero facts are used to simplify denominators.

  -- Tactic 1: field_simp substitute reciproc with denominators into numerator multiplied combination.
  -- Then ring to simplify polynomial in x zero.

  -- Thus key tactics to clear fractions.

  -- After expanding:

  -- $f x - 1 = \frac{(x + a)^2(b - a)(b - c)(c - a)(c - b) + (x + b)^2(a - b)(a - c)(c - a)(c - b) + (x + c)^2(a - b)(a - c)(b - a)(b - c) - (a - b)(a - c)(b - a)(b - c)(c - a)(c - b)}{(a - b)(a - c)(b - a)(b - c)(c - a)(c - b)}$ 

  -- After expanding numerator as degree 1 polynomial to be zero:

  field_simp [h1, h2, h3, h4, h5, h6]
  <;> ring