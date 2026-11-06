import Mathlib

theorem number_theory_189153 (a : ℤ) (n : ℕ) :
    (a ^ 2 + a + 1) ∣ (a + 1) ^ (2 * n + 1) + a ^ (n + 2) := by
  have h1 : ∀ n : ℕ, (a ^ 2 + a + 1) ∣ (a + 1) ^ (2 * n + 1) + a ^ (n + 2) := by
    intro n
    induction n with
    | zero =>
      use 1
      ring
    | succ n ih =>
      have h4 : (a + 1) ^ (2 * (n + 1) + 1) + a ^ ((n + 1) + 2) = 
        (a + 1) ^ (2 * n + 1) * (a + 1) ^ 2 + a * (a ^ (n + 2)) := by 
        ring_nf
      rw [h4]

      -- Show that E = X * Y where E is the expression for n+1 and X is the induction hypothesis expression
      -- From the induction hypothesis: $S = (a + 1) ^ {2n + 1} + a ^ {n + 2}$ is divisible by P = a^2 + a + 1
      -- We need to show R = (a + 1) ^ {2n + 1} * (a + 1)^2 + a * (a^ (n + 2)) is divisible by P.

      -- Notice that R = S * Q where Q = (a + 1)^2, and so P | (S * Q) using the induction hypothesis
      have h6 : (a + 1) ^ (2 * n + 1) * (a + 1) ^ 2 + a * (a ^ (n + 2)) = 
        ( (a + 1) ^ (2 * n + 1) + a ^ (n + 2) ) * ( (a + 1) ^ 2 ) - (a ^ (n + 2) * ( (a + 1) ^ 2 - a )) := by 
        ring_nf
      rw [h6]

      -- From h6, we have R = E1 - E2, where E1 is multiple of the induction hypothesis (which is divisible by P)
      -- so we need to show E2 is also divisible by P. $E2 = a^{n+2} \cdot e$, where e = ( (a+1)^2 -a ) = a^2 +a +1 = P
      -- so E2 is a multiple of P, hence divisible by P.
      have h8 : (a ^ 2 + a + 1) ∣ ((a + 1) ^ (2 * n + 1) + a ^ (n + 2)) * ((a + 1) ^ 2) := by
        have h9 : (a ^ 2 + a + 1) ∣ ((a + 1) ^ (2 * n + 1) + a ^ (n + 2)) := ih
        apply dvd_mul_of_dvd_left h9
      have h10 : (a ^ 2 + a + 1) ∣ (a ^ (n + 2) * ((a + 1) ^ 2 - a)) := by
        have h11 : (a + 1) ^ 2 - a = a ^ 2 + a + 1 := by 
          ring_nf
        rw [h11] 
        use a ^ (n + 2)
        ring
      have h12 : (a ^ 2 + a + 1) ∣ ( ((a + 1) ^ (2 * n + 1) + a ^ (n + 2)) * ((a + 1) ^ 2) - (a ^ (n + 2) * ((a + 1) ^ 2 - a)) ) := by 
        apply Int.dvd_sub 
        · exact h8 
        · exact h10
      exact h12
  specialize h1 n
  simpa using h1