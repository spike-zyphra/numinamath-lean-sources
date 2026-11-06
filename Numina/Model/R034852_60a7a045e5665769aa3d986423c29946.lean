import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_145142 {f : ℝ → ℝ → ℝ → ℝ}
  (hf : f = λ x y z => if y^2 + z^2 ≠ 0 then x^4 + 2 * x * y * z / (y^2 + z^2) else x^4)
  (A : ℝ × ℝ × ℝ) (hA : A = (1, 0, 0)) :
  deriv (λ x => f x (A.2.1) (A.2.2)) 1 = 4 ∧
  deriv (λ y => f (A.1) y (A.2.2)) 0 = 0 ∧
  deriv (λ z => f (A.1) (A.2.1) z) 0 = 0 := by

  have h1 : (λ x => f x (A.2.1) (A.2.2)) = (λ x : ℝ => x^4) := by
    rw [hA]
    funext x
    simp [hf]

  have h2 : deriv (λ x => f x (A.2.1) (A.2.2)) 1 = 4 := by
    rw [h1]
    simp [deriv_pow]

  have h3 : (λ y => f (A.1) y (A.2.2)) = (λ y : ℝ => (1:ℝ)^4) := by
    rw [hA]
    funext y
    simp [hf]

  have h4 : deriv (λ y => f (A.1) y (A.2.2)) 0 = 0 := by
    rw [h3]
    simp [deriv_const]

  have h5 : (λ z => f (A.1) (A.2.1) z) = (λ z : ℝ => (1:ℝ)^4) := by
    rw [hA]
    funext z
    simp [hf]

  have h6 : deriv (λ z => f (A.1) (A.2.1) z) 0 = 0 := by
    rw [h5]
    simp [deriv_const]

  constructor
  · exact h2
  constructor
  · exact h4
  · exact h6