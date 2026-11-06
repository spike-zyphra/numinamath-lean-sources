import Mathlib
/- Let $b$ be an integer base such that $b > 5$.
Let $N$ be the integer whose representation in base $b$ is "454" (meaning $N = 4 \cdot b^2 + 5 \cdot b + 4$). Let $K$ be the integer $5$ (which is $(5)_b$ as $b>5$).
The integer $N$ is divisible by $K$ if and only if $b^2 \equiv -1 \pmod 5$ (i.e., $b \equiv 2 \pmod 5$ or $b \equiv 3 \pmod 5$). Assume this condition holds.

If $b \equiv 2 \pmod 5$, show that the quotient of $N$ by $K$, when expressed as a list of digits in base $b$ (from least significant to most significant), is `[(3*b+4)/5, (4*b+2)/5]`.
If $b \equiv 3 \pmod 5$, show that the quotient of $N$ by $K$, when expressed as a list of digits in base $b$ (from least significant to most significant), is `[(2*b+4)/5, (4*b+3)/5]`. -/
theorem number_theory_642042 (b : ℕ) (hb : b > 5) : (b ≡ 2 [MOD 5] → (4 * b ^ 2 + 5 * b + 4) / 5 = (3 * b + 4) / 5 + (4 * b + 2) / 5 * b) ∧ (b ≡ 3 [MOD 5] → (4 * b ^ 2 + 5 * b + 4) / 5 = (2 * b + 4) / 5 + (4 * b + 3) / 5 * b):= by
  -- Split the proof into two parts using constructor
  constructor
  .
    -- First part: prove the case where b ≡ 2 (mod 5)
    intro h
    -- Convert the modular equivalence to divisibility statement
    replace h : 5 ∣ b - 2:= by
      -- Prove b ≥ 2 using omega tactic
      replace hb : b ≥ 2:= by omega
      exact (Nat.modEq_iff_dvd' hb).mp (id (Nat.ModEq.symm h))
    -- Extract the quotient k where b = 5k + 2
    rcases h with ⟨k, hk⟩
    -- Substitute the expression for b
    replace hk : b = 5 * k + 2:= by omega
    subst b
    -- Algebraic manipulations to prove the equality
    rw [show 4 * (5 * k + 2) ^ 2 + 5 * (5 * k + 2) + 4 = (20 * k ^ 2 + 21 * k + 6) * 5 by ring]
    rw [show 3 * (5 * k + 2) + 4 = (3 * k + 2) * 5 by ring]
    rw [show 4 * (5 * k + 2) + 2 = (4 * k + 2) * 5 by ring]
    norm_num
    ring_nf
  .
    -- Second part: prove the case where b ≡ 3 (mod 5)
    intro h
    -- Convert the modular equivalence to divisibility statement
    replace h : 5 ∣ b - 3:= by
      -- Prove b ≥ 3 using omega tactic
      replace hb : b ≥ 3:= by omega
      exact (Nat.modEq_iff_dvd' hb).mp (id (Nat.ModEq.symm h))
    -- Extract the quotient k where b = 5k + 3
    rcases h with ⟨k, hk⟩
    -- Substitute the expression for b
    replace hk : b = 5 * k + 3:= by omega
    subst b
    -- Algebraic manipulations to prove the equality
    ring_nf
    rw [show 55 + k * 145 + k ^ 2 * 100 = (20 * k ^ 2 + 29 * k + 11) * 5 by ring]
    rw [show 15 + k * 20 = (4 * k + 3) * 5 by ring]
    rw [show 10 + k * 10 = (2 * k + 2) * 5 by ring]
    norm_num
    ring_nf
