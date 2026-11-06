import Mathlib

theorem algebra_33947 : ∃ x, ∀ a b c : ℝ, a ≠ b → a ≠ c → b ≠ c →
    ((b - c)^2 / ((a - b) * (a - c)) + (c - a)^2 / ((b - c) * (b - a)) +
     (a - b)^2 / ((c - a) * (c - b))) = x := by 
  use -3
  intro a b c ha1 ha2 ha3
  have h1 : a - b ≠ 0 := by
    intro h
    apply ha1
    linarith
  have h2 : a - c ≠ 0 := by
    intro h
    apply ha2
    linarith
  have h3 : b - c ≠ 0 := by
    intro h
    apply ha3
    linarith
  have h4 : b - a ≠ 0 := by
    intro h
    apply ha1
    linarith
  have h5 : c - a ≠ 0 := by
    intro h
    apply ha2
    linarith
  have h6 : c - b ≠ 0 := by
    intro h
    apply ha3
    linarith
  field_simp [(show a - b ≠ 0 by assumption), (show a - c ≠ 0 by assumption), (show b - c ≠ 0 by assumption), 
      (show b - a ≠ 0 by assumption), (show c - a ≠ 0 by assumption), (show c - b ≠ 0 by assumption)]
  ring