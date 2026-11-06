import Mathlib
/-Compute the least common multiple of $9999$ and $100{,}001$.-/
theorem number_theory_23426 : lcm 9999 100001 = 90900909 := by
    --Recall the identity $\mathop{\text{lcm}}[a,b]\cdot \gcd(a,b)=ab$, which holds for all positive integers $a$ and $b$. Thus, $$\mathop{\text{lcm}}[9999,100001] = \frac{9999\cdot 100001}{\gcd(9999,100001)},$$so we focus on computing $\gcd(9999,100001)$.
    rw [lcm,instGCDMonoidNat] ;simp ;rw [Nat.lcm]
    have h : Nat.gcd 9999 100001 = 11 := by
      rw [Nat.gcd_rec]
      --Notice that $100001 = 99990+11 = 10(9999)+11$. Therefore, any common divisor of $100001$ and $9999$ must be a divisor of $100001-10\cdot 9999 = 11$. The possibilities are $1$ and $11$.
      have h1 : 100001 % 9999 = 11 := by
        rw [show 100001 = 10 * (9999) + 11 by ring]
      rw [h1]
      rw [Nat.gcd_rec]
      --In fact, $9999=11\cdot 909$, so $11$ is a divisor of $9999$ and $100001$, which gives $\gcd(9999,100001) = 11$.
      have h2 : 9999 % 11 = 0 := by
        rw [show 9999 = 11 * (909) by ring]
      rw [h2]
      simp
    --Therefore, \begin{align\*} \mathop{\text{lcm}}[9999,100001] &= \frac{9999\cdot 100001}{11} \ &= 909\cdot 100001 \ &= 909\cdot 100000 + 909 \ &= \boxed{90{,}900{,}909}. \end{align\*}
    rw [h]

