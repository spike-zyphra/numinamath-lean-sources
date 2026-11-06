import Mathlib
/- Theorem. Let $A$ and $B$ be two positive integers. Then there exists a positive integer $k$ such that $\gcd(A,B) = \gcd(A+k, B) = \gcd(A, B+k) = \gcd(A+k, B+k)$.

To verify with small numbers, let $A=6$ and $B=10$.
Then $\gcd(A,B) = \gcd(6,10)=2$.
Let $g_640642 = \gcd(A,B) = 2$. Let $A=g_640642 A'$ and $B=g_640642 B'$. So $A'=3, B'=5$.
We need to find a positive integer $m$ such that $k=g_0m$ satisfies the conditions. The conditions derived are:
1. $\gcd(A'+m, B'-A')=1$. Here $\gcd(3+m, 5-3) = \gcd(3+m, 2)=1$. This means $3+m$ must be odd, so $m$ must be even.
2. $\gcd(A'+m, B')=1$. Here $\gcd(3+m, 5)=1$. This means $3+m \not\equiv 0 \pmod 5$, so $m \not\equiv -3 \equiv 2 \pmod 5$.
3. $\gcd(A', B'+m)=1$. Here $\gcd(3, 5+m)=1$. This means $5+m \not\equiv 0 \pmod 3$, so $m \not\equiv -5 \equiv 1 \pmod 3$.

We need $m$ such that: $m$ is even, $m \not\equiv 2 \pmod 5$, and $m \not\equiv 1 \pmod 3$.
Let's test values of $m$:
- $m=2$: Is even. $2 \equiv 2 \pmod 5$. Fails.
- $m=4$: Is even. $4 \not\equiv 2 \pmod 5$. $4 \equiv 1 \pmod 3$. Fails.
- $m=6$: Is even. $6 \equiv 1 \pmod 5 \not\equiv 2 \pmod 5$. $6 \equiv 0 \pmod 3 \not\equiv 1 \pmod 3$. This works.
So $m=6$ is a possible value. This gives $k = g_640642 m = 2 \times 6 = 12$.
Let's check for $k=12$:
$\gcd(6,10)=2$.
$\gcd(6+12, 10) = \gcd(18,10)=2$.
$\gcd(6, 10+12) = \gcd(6,22)=2$.
$\gcd(6+12, 10+12) = \gcd(18,22)=2$.
All conditions hold for $k=12$. Thus, such a $k$ exists. -/
theorem number_theory_640642 (a b : ℤ) (ha : a > 0) (hb : b > 0) : ∃ k : ℤ, Int.gcd a b = Int.gcd (a + k) b ∧ Int.gcd a b = Int.gcd a (b + k) ∧ Int.gcd a b = Int.gcd (a + k) (b + k):= by
  -- Set d as the gcd of a and b
  set d:= Int.gcd a b with hd
  -- Clear the definition of d to work with the hypothesis
  clear_value d
  -- Prove that d divides a
  have ga : (↑d : ℤ) ∣ a:= by
    subst d
    exact Int.gcd_dvd_left
  -- Prove that d divides b
  have gb : (↑d : ℤ) ∣ b:= by
    subst d
    exact Int.gcd_dvd_right
  -- Express a and b as multiples of d
  rcases ga with ⟨a, rfl⟩
  rcases gb with ⟨b, rfl⟩
  -- Choose k = (a - b) * a * b * d as our candidate
  use (a - b) * a * b * d
  -- Rewrite the gcd expression using the fact that d is the gcd
  rw [Int.gcd_mul_left (↑d : ℤ) a b] at hd
  simp at hd
  -- Prove that d is positive
  have hdpos : d > 0:= by
    by_contra H
    simp at H
    subst d
    simp at ha
  -- Show that the gcd of the coprime parts equals d
  replace hd : d * (a.gcd b) = d:= by rw [←hd]
  -- Conclude that a and b are coprime
  replace hd : a.gcd b = 1:= by exact (Nat.mul_right_eq_self_iff hdpos).mp hd
  -- Convert to IsCoprime for easier manipulation
  replace hd : IsCoprime a b:= by exact Int.isCoprime_iff_gcd_eq_one.mpr hd
  -- Prove the three required equalities
  refine ⟨?_, ?_, ?_⟩
  .
    -- First goal: gcd(a,b) = gcd(a+k,b)
    rw [show ↑d * a + (a - b) * a * b * ↑d = ↑d * (a + (a - b) * a * b) by ring]
    rw [Int.gcd_mul_left (↑d : ℤ) _ _]
    simp
    -- Show that the coprime part has gcd 1
    have g1 : Int.gcd (a + (a - b) * a * b) b = 1:= by
      refine Int.isCoprime_iff_gcd_eq_one.mp ?_
      exact IsCoprime.add_mul_right_left_iff.mpr hd
    rw [g1]
    simp
  .
    -- Second goal: gcd(a,b) = gcd(a,b+k)
    rw [show ↑d * b + (a - b) * a * b * ↑d = d * (b + (a - b) * a * b) by ring]
    rw [Int.gcd_mul_left (↑d : ℤ) _ _]
    simp
    -- Show that the coprime part has gcd 1
    have g1 : Int.gcd a (b + (a - b) * a * b) = 1:= by
      refine Int.isCoprime_iff_gcd_eq_one.mp ?_
      rw [show (a - b) * a * b = (a - b) * b * a by ring]
      exact IsCoprime.add_mul_right_right_iff.mpr hd
    rw [g1]
    simp
  .
    -- Third goal: gcd(a,b) = gcd(a+k,b+k)
    rw [show ↑d * a + (a - b) * a * b * ↑d = d * (a + (a - b) * a * b) by ring]
    rw [show ↑d * b + (a - b) * a * b * ↑d = d * (b + (a - b) * a * b) by ring]
    rw [Int.gcd_mul_left (↑d : ℤ) _ _]
    simp
    -- Show that the coprime parts have gcd 1
    have g1 : Int.gcd (a + (a - b) * a * b) (b + (a - b) * a * b) = 1:= by
      refine Int.isCoprime_iff_gcd_eq_one.mp ?_
      rw [show b + (a - b) * a * b = b * (1 + (a - b) * a) by ring]
      -- Show that (a + (a-b)*a*b) and b are coprime
      have g1 : IsCoprime (a + (a - b) * a * b) b:= by exact IsCoprime.add_mul_right_left_iff.mpr hd
      -- Show that (a + (a-b)*a*b) and (1 + (a-b)*a) are coprime
      have g2 : IsCoprime (a + (a - b) * a * b) (1 + (a - b) * a):= by
        rw [show a + (a - b) * a * b = a - b + b * (1 + (a - b) * a) by ring]
        -- Use the fact that (a-b) and 1 are coprime
        suffices IsCoprime (a - b) (1 + (a - b) * a) by exact IsCoprime.add_mul_right_left_iff.mpr this
        suffices IsCoprime (a - b) 1 by exact IsCoprime.add_mul_left_right this a
        exact isCoprime_one_right
      -- Combine the coprimality results
      exact IsCoprime.mul_right g1 g2
    rw [g1]
    simp
