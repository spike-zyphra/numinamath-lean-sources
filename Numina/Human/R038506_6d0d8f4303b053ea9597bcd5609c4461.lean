import Mathlib

namespace number_theory_134915

def a (n : ℕ) : ℤ := match n with
| 0 => 0
| 1 => 1
| n + 2 => 4 * a (n + 1) - a n

def b (n : ℕ) : ℤ := match n with
| 0 => 1
| 1 => 2
| n + 2 => 4 * b (n + 1) - b n

end number_theory_134915

open number_theory_134915

/- 20th CanMO 1988 Problem 4 Define two integer sequences a 0 , a 1 , a 2 , ... and b 0 , b 1 , b 2 , ... as follows. a 0 = 0, a 1 = 1, a n+2 = 4a n+1 - a n , b 0 = 1, b 1 = 2, b n+2 = 4b n+1 - b n . Show that b n 2 = 3a n 2 + 1. -/
theorem number_theory_134915 (n : ℕ) : (b n)^2 = 3 * (a n)^2 + 1 :=
  -- use induction to show that
  -- b(n)^2 = 3 * a(n)^2 + 1 and b(n + 1) * b(n) = 3 * a(n + 1) * a(n) + 2
  let rec f : (n : ℕ) → b n ^ 2 = 3 * a n ^ 2 + 1 ∧ b (n + 1) * b n = 3 * a (n + 1) * a n + 2
  | 0 => by simp [a, b]
  | 1 => by simp [a, b]
  | n + 2 => by
    simp [a, b]
    -- we have induction hypotheses:
    -- ih1: b(n + 1)^2 = 3 * a(n + 1)^2 + 1
    -- ih3: b(n)^2 = 3 * a(n)^2 + 1
    -- ih4: b(n + 1) * b(n) = 3 * a(n + 1) * a(n) + 2
    have ⟨ih1, ih2⟩ := f (n + 1)
    have ⟨ih3, ih4⟩ := f n
    constructor
    -- prove that b(n + 2)^2 = 3 * a(n + 2)^2 + 1
    · rw [show ∀ (x y : ℤ), (4 * x - y) ^ 2 = 16 * x ^ 2 + y ^ 2 - 8 * (x * y) by intros; ring]
      rw [ih1, ih3, ih4]
      ring
    -- prove that b(n + 3) * b(n + 2) = 3 * a(n + 3) * a(n + 2) + 2
    · ring_nf
      rw [show 1 + n = n + 1 by ring, ih4, ih1, ih3]
      ring
  (f n).1