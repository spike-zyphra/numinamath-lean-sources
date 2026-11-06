import Mathlib
/- Let $u$ and $v$ be positive integers, and let $B$ be an odd integer greater than $1$. Show that the number $N = 2^{4u+2} + B^{4v}$ is a composite number. -/
theorem number_theory_640192 (u v b : ℕ) (hb : Odd b) (hu : u > 0) (hv : v > 0) : ¬(Nat.Prime (2 ^ (4 * u + 2) + b ^ (4 * v))):= by
  -- First prove that the number is positive
  have h : 2 ^ (4 * u + 2) + b ^ (4 * v) > 0:= by positivity

  -- Define two factors x and y that will multiply to give our number
  -- x = (b^v)^2 + 2*(2^u)^2 + 2*b^v*2^u
  set x:= (b ^ v) ^ 2 + 2 * (2 ^ u) ^ 2 + 2 * b ^ v * 2 ^ u with hx
  -- y = (b^v)^2 + 2*(2^u)^2 - 2*b^v*2^u
  set y:= (b ^ v) ^ 2 + 2 * (2 ^ u) ^ 2 - 2 * b ^ v * 2 ^ u with hy
  clear_value x y

  -- Prove that x * y equals our original number
  have g1 : x * y = 2 ^ (4 * u + 2) + b ^ (4 * v):= by
    -- Introduce substitutions for cleaner algebra
    set A:= 2 ^ u with hA
    set B:= b ^ v with hB
    clear_value A B

    -- Show that 2^(4u+2) = 4*A^4
    have g2 : 2 ^ (4 * u + 2) = 4 * A ^ 4:= by
      subst A
      ring_nf

    -- Show that b^(4v) = B^4
    have g3 : b ^ (4 * v) = B ^ 4:= by
      subst B
      ring_nf
    rw [g2, g3]
    clear g2 g3

    -- Prove inequality needed for factorization
    have g2 : B ^ 2 + 2 * A ^ 2 ≥ 2 * B * A:= by
      rify
      suffices ((↑A : ℝ) - B) ^ 2 + A ^ 2 ≥ 0 by linarith
      positivity
    rify at hx hy
    field_simp at hx hy
    rify
    rw [hx, hy]
    ring_nf

  -- Use the fact that if a number is product of two factors > 1, it's composite
  refine Nat.not_prime_mul' g1 ?_ ?_
  .
    -- Prove first factor x ≥ 2
    have g2 : x ≥ 2:= by
      subst x
      have g3 : (2 ^ u) ^ 2 > 0:= by positivity
      omega
    omega
  .
    -- Prove second factor y ≥ 2
    have g3 : y ≥ 2:= by
      subst y
      suffices (b ^ v) ^ 2 + 2 * (2 ^ u) ^ 2 ≥ 2 * b ^ v * 2 ^ u + 2 by omega
      rify
      suffices ((b : ℝ) ^ v - 2 ^ u) ^ 2 + (2 ^ u) ^ 2 ≥ 2 by linarith
      have g1 : ((b : ℝ) ^ v - 2 ^ u) ^ 2 ≥ 0:= by positivity
      have g2 : (2 ^ u) ^ 2 ≥ 2:= by
        set u1:= u - 1 with hu1
        clear_value u1
        replace hu1 : u = u1 + 1:= by omega
        subst u
        ring_nf
        have g2 : 2 ^ (u1 * 2) > 0:= by positivity
        linarith
      rify at g2
      linarith
    omega
