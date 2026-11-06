import Mathlib

theorem algebra_6256 (f g : ℝ → ℝ)
    (hf : f = fun x => x ^ 2 - 5 * x + 11)
    (hg : g = fun x => -x ^ 2 + 3 * x + 5) :
    ∀ x, f x = g x ↔ x = 1 ∨ x = 3 := by
  intro x
  rw [hf, hg]
  simp
  constructor
  · -- Assume $f(x) = g(x)$, we need to prove $x = 1 \lor x = 3$
    intro h
    have h1 : x ^ 2 - 4 * x + 3 = 0 := by linarith
    have h2 : (x - 1) * (x - 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- Case x - 1 = 0, so x = 1
      left
      linarith
    · -- Case x - 3 = 0, so x = 3
      right
      linarith
  · -- Assume x = 1 or x = 3, prove f(x) = g(x)
    rintro (h | h)
    · -- Case x = 1
      rw [h]
      norm_num
    · -- Case x = 3
      rw [h]
      norm_num