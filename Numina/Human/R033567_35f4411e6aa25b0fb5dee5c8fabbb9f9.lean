import Mathlib

/-- Adults made up $\frac5{12}$ of the crowd of people at a concert. After a bus carrying $50$ more
people arrived, adults made up $\frac{11}{25}$ of the people at the concert. Find the minimum
number of adults who could have been at the concert after the bus arrived. -/
theorem algebra_25522 :
    IsLeast
    ((fun ⟨a, a'⟩ ↦ a + a') '' {(a, a') : ℕ × ℕ | ∃ c c', a + c ≠ 0 ∧ 12 * a = 5 * (a + c) ∧ a' + c' = 50 ∧
    25 * (a + a') = 11 * (a + c + 50)})
    154 := by

  -- Let $a$ be the number of adults at the party before the bus arrives.
  -- Let $c$ be the number of children at the party before the bus arrives.
  -- Let $a'$ be the number of adults in the bus.
  -- Let $c'$ be the number of children in he bus.
  -- Therefore, the quantity we want to minimize, the number of adults after the bus arrives, is
  -- $a + a'$. We claim that this minimum is 154.

  constructor
  -- To see that the minimum value 154 is really achived, consider the assignments, $a = 125$,
  -- $a' = 29$, $c = 175$ and $c' = 21$. It is a matter of simple algebra to see that these values
  -- satisfies all the constraints.
  · simp
    exact ⟨125, 29, ⟨175, by trivial, rfl, ⟨21, rfl⟩, rfl⟩, rfl⟩

  -- To show that nothing smaller 154 can be achieved, let $x$ be an achived value.
  · simp only [lowerBounds, Set.mem_image]
    -- Then, there exists $a, a', c, c'$ satisfying the constraints and $x = a + a'$.
    rintro x ⟨⟨a, a'⟩, ⟨c, c', h1, h2, h3, h4⟩, rfl⟩
    dsimp at h1 h2 h3 h4 ⊢

    -- We want to show that $154 \leq a + a'$. From the equation $25 (a + a') = 11 (a + c + 50)$,
    -- it is enough to show that $300 \leq a + c$.
    suffices 300 ≤ a + c from by clear * - this h4; omega

    -- Because $a$ and $c$ are nonzero, to show that $300 \leq a + c$, it is enough to show that
    -- $300 | a + c$.
    suffices 300 ∣ a + c from by clear * - this h1; omega

    -- Observe that $300 = 12 \cdot 25$, and 12 and 25 are coprime, so it is enough to show that
    -- $a + c$ is divisible by 12 and 25.
    suffices 12 ∣ a + c ∧ 25 ∣ a + c from by clear * - this; omega
    constructor

    -- First, let's show that it is divisible by 12. Because 5 and 12 are coprime, it is enough
    -- to show that $5 (a + c)$ is divisible by 12.
    · suffices 12 ∣ 5 * (a + c) from by clear * - this; omega
      -- This immediate from the equation $12 a = 5 (a + c)$
      use a
      exact h2.symm

    -- Lastly, let's show that $a + c$ is divisible by 25. Because 11 and 25 are coprime, it is
    -- enough to show that $11 (a + c)$ is divisible by 25.
    · suffices 25 ∣ 11 * (a + c) from by clear * - this; omega
      -- This is immediate from the eqation $25 (a + a') = 11 (a + c + 50)$ because 50 is divisible
      -- by 25.
      use a + a' - 22
      rw [Nat.mul_sub, h4]
      clear * - a c
      omega