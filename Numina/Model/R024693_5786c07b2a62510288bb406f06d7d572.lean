import Mathlib

def f (a b : ℝ) := a ^ 2 * b - a * b ^ 2

theorem algebra_8243 : {(x, y) : ℝ × ℝ | f x y = f y x} =
    {(x, y) : ℝ × ℝ | x = 0 ∨ y = 0 ∨ x = y} := by
  ext ⟨x, y⟩
  simp [f]
  constructor
  · -- First direction: if $f x y = f y x$ then $(x, y)$ satisfies $x = 0$ or $y = 0$ or $x = y$.
    intro h
    have h1 : x * y * (x - y) = 0 := by
      nlinarith 
    cases' (mul_eq_zero.mp h1) with h2 h3
    · -- Case x * y = 0
      cases' (mul_eq_zero.mp h2) with h4 h5
      · -- Case x = 0
        left
        linarith
      · -- Case y = 0
        right
        left
        linarith
    · -- Case x - y = 0
      right
      right
      linarith
  · -- Second direction: if $x = 0$ or $y = 0$ or $x = y$ then $f x y = f y x$.
    rintro (h | h | h)
    · -- Case x = 0
      rw [h]
      all_goals nlinarith
    · -- Case y = 0
      rw [h]
      all_goals nlinarith
    · -- Case x = y
      have h1 : x = y := by linarith
      rw [show y = x by linarith [h1]]
      all_goals nlinarith