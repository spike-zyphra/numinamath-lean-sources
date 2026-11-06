import Mathlib

/-If $a$ is a constant such that $9x^2 + 24x + a$ is the square of a binomial, then what is $a$?-/
theorem algebra_11102 (a : ℝ) (h : ∃ b, ∀x, (9 * x ^ 2 + 24 * x + a) = (b + 3 * x) ^ 2) :
    a = 16 := by
  -- If $9x^2 +24x + a$ is the square of a binomial, then the binomial has the form $3x +b$ for some number $b$, because $(3x)^2 = 9x^2$.  So, we compare $(3x+b)^2$ to $9x^2 + 24x + a$. Expanding $(3x+b)^2$ gives \[(3x+b)^2 = (3x)^2 + 2(3x)(b) + b^2 = 9x^2 + 6bx + b^2.\]Equating the linear term of this to the linear term of $9x^2+24x+a$, we have $6bx=24x$, so $b=4$.  Equating the constant term of $9x^2 + 6bx + b^2$ to that of $9x^2 + 24x+a$ gives us $a=b^2 = \boxed{16}$.
  rcases h with ⟨b, hb⟩
  have : ∀x, (9 * x ^ 2 + 24 * x + a) = 9 * x ^ 2 + 6 * b * x + b ^ 2 := by
    intro x
    rw [hb x]
    ring_nf
  -- specialize this 0, so, we could get a = b^2
  have hb' : b^2 = a := by
    specialize this 0
    simp at this
    exact this.symm
  -- because a = b^2, specialize this 1, replace a with b^2, and we could get b = 4
  have hb : b = 4 := by
    specialize this 1
    simp at this
    rw [hb'] at this
    simp at this
    linarith
  rw [hb] at hb'
  linarith
