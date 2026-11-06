import Mathlib

/-- In the United States, coins have the following thicknesses: penny, $1.55$ mm; nickel, $1.95$ mm;
dime, $1.35$ mm; quarter, $1.75$ mm. If a stack of these coins is exactly $14$ mm high, how many
coins are in the stack?

$\mathrm{(A) \ } 7 \qquad \mathrm{(B) \ } 8 \qquad \mathrm{(C) \ } 9 \qquad \mathrm{(D) \ } 10
\qquad \mathrm{(E) \ } 11$ -/
theorem number_theory_95343 (p n d q : ℕ)
    (h : p * (1.55 : ℚ) + n * (1.95 : ℚ) + d * (1.35 : ℚ) + q * (1.75 : ℚ) = 14) :
    p + n + d + q = 8 := by

  -- Let $p$, $n$, $d$, and $q$ be the number of pounds, nickels, dimes, and quarters respectively.

  -- Multiplying our equation by 100, we get $155p + 195n + 135d + 175q = 1400$.
  replace h : p * 155 + n * 195 + d * 135 + q * 175 = 1400 := by qify; linarith

  -- We can divide the equation by 5 to get $31p + 39n + 27d + 35q = 280$.
  replace h : p * 31 + n * 39 + d * 27 + q * 35 = 280 := by linarith

  -- Let $T = p + n + d + q$, the number of coins.
  set T := p + n + d + q

  -- First, let's show that $T \leq 10$.
  have hT1 : T ≤ 10 := by
    -- To that end, it is enough to show that $27 T \leq 280$.
    suffices 27 * T ≤ 280 by omega
    -- we have:
    -- 27 T = p 27 + n 27 + d 27 + q 27
    calc _ = p * 27 + n * 27 + d * 27 + q * 27 := by simp [T]; ring
    -- \leq p 31 + n 39 + d 27 + q 35 = 280 because each variable is nonnegative.
         _ ≤ p * 31 + n * 39 + d * 27 + q * 35 := by linarith
    -- = 280 by our equation.
         _ = 280 := by assumption

  -- Similarly, let's show that $T \geq 8$.
  have hT2 : 8 ≤ T := by
    -- To that end, it is enough to show that $39 T \geq 280$.
    suffices 280 ≤ 39 * T by omega
    -- we have:
    -- 280 = p 31 + n 39 + d 27 + q 35 by our equation.
    calc _ = p * 31 + n * 39 + d * 27 + q * 35 := by exact h.symm
    -- \leq p 39 + n 39 + d 39 + q 39 = 39 T because each variable is nonnegative.
         _ ≤ p * 39 + n * 39 + d * 39 + q * 39 := by linarith
    -- = 39 T by definition of $T$.
         _ = _ := by simp [T]; ring

  -- Therefore, $T$ is either $8$, $9$, or $10$.
  interval_cases hT : T

  -- If it is $8$, we are done. Let's show that the other two cases are impossible.
  · rfl

  -- For a contradiction, assume that $T = 9$.
  · exfalso
    -- We have $280 = p 31 + n 39 + d 27 + q 35 = T 27 + p 4 + n 12 + q 8$.
    replace h : T * 27 + p * 4 + n * 12 + q * 8 = 280 := by simp [T, ←h]; ring

    -- Every term in this equation ecxept $T 27$ is divisible by $2$, so $T 27$ is also divisible by
    -- $2$.
    have : 2 ∣ 27 * T := by
      zify at h ⊢
      use (140: ℤ) - p * 2 - n * 6 - q * 4
      ring_nf
      simp [T, ←h]
      ring

    -- Because $2$ is prime and $27$ is not divisible by $2$, $T$ is divisible by $2$.
    have : 2 ∣ T := by
      rw [Nat.Prime.dvd_mul (by norm_num)] at this
      rcases this with (h | h)
      · norm_num at h
      · exact h

    -- However, $9$ is not divisible by $2$, a contradiction.
    rw [hT] at this
    norm_num at this

  -- Now, for a contradiction, assume that $T = 10$.
  · exfalso
    -- We have $280 = p 31 + n 39 + d 27 + q 35 = T 27 + p 4 + n 12 + q 8$.
    replace h : T * 27 + p * 4 + n * 12 + q * 8 = 280 := by simp [T, ←h]; ring
    -- Substituting $T = 10$, we get $10 27 + p 4 + n 12 + q 8 = 280$.
    simp [hT] at h
    -- This simplifies to $p 4 + n 12 + q 8 = 10$.
    replace h : p * 4 + n * 12 + q * 8 = 10 := by linarith
    -- Dividing both sides by $2$, we get $p 2 + n 6 + q 4 = 5$.
    replace h : p * 2 + n * 6 + q * 4 = 5 := by linarith

    -- Every term in this equation ecxept $5$ is divisible by $2$, so $5$ is also divisible by
    -- $2$.
    have : 2 ∣ 5 := by
      use p + n * 3 + q * 2
      rw [←h]
      ring

    -- However, $5$ is not divisible by $2$, a contradiction.
    norm_num at this