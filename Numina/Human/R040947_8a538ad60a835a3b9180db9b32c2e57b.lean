import Mathlib

/- Indicate in which one of the following equations y is neither directly nor inversely proportional to x:
(A) x+y=0   (B) 3xy=10    (C) x=5y    (D) 3x+y=10   (E)x/y=√3 -/
theorem algebra_93610 (x y: ℝ) (hy : y ≠ 0) : 
(∃ k : ℝ , x + y = 0 → (y = k * x ∨ x * y = k)) ∧
(∃ k : ℝ , 3*x*y = 10 → (y = k * x ∨ x * y = k)) ∧ 
(∃ k : ℝ , x = 5*y → (y = k * x ∨ x * y = k)) ∧ 
(∃ k : ℝ , x/y = √3 → (y = k * x ∨ x * y = k)) := by
--we proceed by showing the constant of direct or inverse proportionality in the other answers
constructor
--in the first one y is directly proportional of constant -1
· use (-1 : ℝ)
  ring_nf
  intro h
--prove direct proportionality
  left
  linarith
· constructor
--in the second one y is inversely proportional of constant 10/3
  · use (10 / 3 : ℝ)
    intro h
--prove inverse proportionality
    right
    linarith
  · constructor
--in the third one y is directly proportional of constant 1/5
    · use (1/5 : ℝ)
      intro h
--prove direct proportionality
      left
      linarith
--in the fifth one y is directly proportional of constant 1/√3
    · use (1/√3 : ℝ)
      intro h
--prove direct proportionality
      left
      rw [div_eq_iff_mul_eq hy] at h
      norm_num
      field_simp
      linarith