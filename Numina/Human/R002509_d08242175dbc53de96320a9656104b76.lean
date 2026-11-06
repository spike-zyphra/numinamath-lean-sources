import Mathlib

open Set

/-- The number of pairs of positive integers $(x,y)$ which satisfy the equation $x^2+y^2=x^3$ is

$\text {(A)} 0 \qquad  \text {(B)} 1 \qquad  \text {(C)} 2 \qquad  \text {(D)} \text{not finite}
\qquad  \text {(E)} \text{none of these}$ -/
theorem algebra_94404 :
    {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ^ 2 + y ^ 2 = x ^ 3}.Infinite := by

  -- Let $s$ be the set of all pairs of positive integers $(x, y)$ such that $x^2 + y^2 = x^3$.
  set s := {(x, y) : ℕ × ℕ | x > 0 ∧ y > 0 ∧ x ^ 2 + y ^ 2 = x ^ 3}

  -- Notice that $y^2 = x^3 - x^2 = x^2 (x - 1)$.
  have {x y : ℕ} (hx : x > 0) (hy : y > 0) : y^2 = x^3 - x^2 ↔ y^2 = x^2 * (x - 1) := by
    constructor <;> {
      intro h
      rw [h, Nat.mul_sub, mul_one]; rfl
    }

  -- This shows that when $x - 1 = a^2$ for some natural numbers $a$ i.e., when $x - 1$ is a perfect
  -- square, $y$ is determined as $x a$.

  -- Then, let $f$ be the function that maps $a$ to $(a^2 + 1, (a^2 + 1) a)$.
  let f (a : ℕ) := (a^2 + 1, (a^2 + 1) * a)

  -- To show that $s$ is infinite, it suffices to find an infinite subset. We claim that the image
  -- of $f$ on the set of positive natural numbers is infinite and contained in $s$.
  suffices (f '' Ici 1).Infinite ∧ f '' Ici 1 ⊆ s by apply Infinite.mono this.2 this.1

  constructor
  -- First, let's show that the image of $f$ on the set of positive natural numbers is infinite. To
  -- that end, it is enough to show that $f$ is injective because the set of positive natural
  -- numbers is infinite.
  · apply Infinite.image ?_ (Ici_infinite 1)

    -- Let $a$, $a'$ be two natural numbers such that $f(a) = f(a')$. As the addition and power operations
    -- are injective, we have $a = a'$.
    rintro a ha a' ha' h
    simp [f] at h
    exact h.1

  -- Lastly, we need to show that the range of $f$ is contained in $s$. Let $(x, y)$ be an element of
  -- the range of $f$.
  · rintro ⟨x, y⟩ ⟨a, ha, haxy⟩

    -- That is to say there exists a positive natural number $a$ such that $x = a^2 + 1$ and
    -- $y = a(a^2 + 1)$.
    simp at ha
    simp [f] at haxy

    refine ⟨?_, ?_, ?_⟩

    -- $x = a^2 + 1$ is positive because the square of a natural number is positive.
    · omega

    -- $y = a(a^2 + 1) = a x$ is positive because both $a$ and $x$ are positive.
    · nlinarith

    -- Lastly, let's check whether $(x, y)$ satisfies the equation $x^2 + y^2 = x^3$.
    · rw [←haxy.1, ←haxy.2]
      -- Substituting $x = a^2 + 1$ and $y = a(a^2 + 1)$ into the equation, and then rearranging
      -- we see that the equation holds.
      ring

  -- This completes the proof that $s$ is infinite.