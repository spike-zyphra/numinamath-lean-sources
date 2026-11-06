import Mathlib

/- Let $a, b, c$ be integers and $m$ be a natural number greater than 1.

If $a^n+bn+c \equiv 0(\bmod m)$ for every natural number $n$, prove that $b^2 \equiv 0(\bmod m)$.
-/
theorem number_theory_248062 {m : ℕ} {a b c : ZMod m}
  (h : ∀ n : ℕ, a ^ n + b * n + c = 0) :
  b ^ 2 = 0 := by
  -- use assumption for n = 1 and n = 2 and eliminate c
  have eq1 : b = a - a^2 := by calc
    b = (a^2 + b * 2 + c) - (a^1 + b * 1 + c) + a - a^2 := by ring
              _ = 0 - 0 + a - a^2 := by nth_rewrite 1 [←h 2]; nth_rewrite 1 [←h 1]; ring
              _ = a - a^2 := by simp
  -- use assumption for n = 2 and n = 3 and eliminate c
  have eq2 : a^3 - a^2 + b = 0 := by calc
    a^3 - a^2 + b = (a^3 + b * 3 + c) - (a^2 + b * 2 + c) := by ring
                _ = 0 - 0 := by nth_rewrite 1 [←h 3]; nth_rewrite 1 [←h 2]; ring
                _ = 0 := by simp
  -- use these equations to eliminate b
  have eq3 : a * (a - 1)^2 = 0 := by calc
    a * (a - 1)^2 = (a^3 - a^2 + b) + (a - a^2) - b := by ring
                _ = 0 := by rw [eq2, eq1]; simp
  -- we must have b^2 = 0
  calc
    b^2 = a * (a - 1)^2 * a := by rw [eq1]; ring
      _ = 0 := by rw [eq3]; ring