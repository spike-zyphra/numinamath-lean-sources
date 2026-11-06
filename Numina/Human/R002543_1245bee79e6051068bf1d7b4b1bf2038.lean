import Mathlib

/-- The average value of all the pennies, nickels, dimes, and quarters in Paula's purse is $20$
cents. If she had one more quarter, the average value would be $21$ cents. How many dimes does she
have in her purse?

$\text {(A)}\ 0 \qquad \text {(B)}\ 1 \qquad \text {(C)}\ 2 \qquad \text {(D)}\ 3\qquad \text
{(E)}\ 4$ -/
theorem algebra_95097 (p n d q : ℕ) (h₀ : p + n + d + q > 0)
    (h₁ : (p + n + d + q) * 20 = p + 5 * n + 10 * d + 25 * q)
    (h₂ : (p + n + d + q + 1) * 21 = p + 5 * n + 10 * d + 25 * (q + 1)) :
    d = 0 := by

  -- Let $N$ be the total number of coins.
  set N := p + n + d + q

  -- Let $v$ be the total value of the coins at the beginning.
  set V := p + 5 * n + 10 * d + 25 * q

  -- From the first equation, we have $V = 20 N$.
  have hVN1 : V = 20 * N := by rw [←h₁]; ring

  -- From the second equation, we have $V + 25 = 21 (N + 1)$
  have hVN2 : V + 25 = 21 * (N + 1) := by rw [mul_comm, h₂]; ring

  -- Canceling $V$ from both equations, we have $20 N + 25 = 21 (N + 1)$
  have hVN3 : 20 * N + 25 = 21 * (N + 1) := by rw [←hVN1, hVN2]

  -- Solving for $N$, we have $N = 4$.
  have hN : N = 4 := by omega

  -- Substituting $N = 4$ into the first equation, we have $V = 80$.
  have hV : V = 80 := by omega

  -- In summmary, we have $4 = p + n + d + q$ and $80 = 100 p + 50 n + 10 d + 25 q$.
  have h₃ : 4 = p + n + d + q := by rw [←hN]
  have h₄ : 80 = p + 5 * n + 10 * d + 25 * q := by rw [←hV]

  -- Notice that from the second equation, we have $p = 80 - 5n - 10d - 25q$, so $p$ is divisible by
  -- $5$.
  have : 5 ∣ p := by omega
  -- However, from the first equation, we have $p = 4 - n - d - q$, so $p < 5$.
  have : p < 5 := by omega
  -- Therefore, $p = 0$.
  have hp : p = 0 := by omega

  -- Substituting $p = 0$ into the equations, we have $n + d + q = 4$ and $50 n + 10 d + 25 q = 80$.
  subst hp; simp at h₃ h₄

  -- We can simplify the second equation by dividing by $5$ and get $16 = n + 2 d + 5 q$.
  replace h₄ : 16 = n + 2 * d + 5 * q := by omega

 -- Subtract the first equation from the second equation and get $12 = d + 4 q$.
  replace h₄ : 12 = d + 4 * q := by omega

  -- From the second equation, we have $d = 12 - 4 q$, so $d$ is divisible by $4$.
  have : 4 ∣ d := by omega
  -- From the first equation, we have $d = 4 - q$, so $d ≤ 4$.
  have : d ≤ 4 := by omega
  -- Therefore, $d = 0$ or $d = 4$.
  have : d = 0 ∨ d = 4 := by omega

  rcases this with (rfl | rfl)
  -- If it is $d = 0$, we are done.
  · rfl

  -- For a contradiction, assume $d = 4$.
  · exfalso
    -- From the first equation, we have $n = 0$ and $q = 0$.
    have : n = 0 := by omega
    have : q = 0 := by omega
    -- But then, the second equation becomes $12 = 4$, which is a contradiction.
    omega