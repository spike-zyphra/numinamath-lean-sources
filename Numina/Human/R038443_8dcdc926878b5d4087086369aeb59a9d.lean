import Mathlib

/- \section*{Problem 2 - 271032}

Let $a$ be a given positive real number.

For a function $f$ defined for all real numbers $x$, it is assumed that it satisfies the following conditions (1) and (2):

(1) For every real number $x$, $f(x) + f(x + a) = 1$.

(2) There exists a real number $c$ such that for all real numbers $x$ that satisfy $c < x < c + \frac{1}{2}$, $f(x) < \frac{1}{2}$ holds.

Prove that from these assumptions it always follows:

The function $f$ is periodic; there is a smallest possible period of $f$.

Determine this smallest possible period of $f$.

Hint:

A function $f$ is called periodic if and only if there exists a positive real number $p$ such that for all real numbers $x$, the equation $f(x + p) = f(x)$ holds.

If this is the case, then any positive real number $p$ for which this holds is called a period of $f$. -/
theorem algebra_190645 (a : ℝ) (ha : 0 < a) (f : ℝ → ℝ)
    (h1 : ∀ x, f x + f (x + a) = 1) (h2 : ∃ c, ∀ x, c < x ∧ x < c + a → f x < 1/2) :
    IsLeast {T | 0 < T ∧ ∀ x, f (x + T) = f x} (2 * a) := by
  -- show that f has period 2 * a
  have period_2a : ∀ x, f (x + 2 * a) = f x
  · intro x
    rw [two_mul, ←add_assoc]
    linarith [h1 x, h1 (x + a)]
  -- show that the least period is 2 * a
  constructor
  · simp only [Set.mem_setOf_eq, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    constructor
    · assumption
    exact period_2a
  rcases h2 with ⟨c, hc⟩
  intro p hp
  simp only [Set.mem_setOf_eq] at hp
  by_contra hp_2a
  -- we use the points below to show a contradiction with the condition f x < 1/2
  have hx := hc (c - p/2 + p) ⟨by linarith, by linarith⟩
  have hx' := hc (c - p/2 + a) ⟨by linarith, by linarith⟩
  have := calc
    f (c - p/2 + p) + f (c - p/2 + a) = f (c - p/2) + f (c - p/2 + a) := by rw [hp.2 (c - p/2)]
    _ = 1 := h1 (c - p/2)
  linarith