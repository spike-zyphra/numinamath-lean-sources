import Mathlib

/-- When the natural numbers $P$ and $P'$, with $P>P'$, are divided by the natural number $D$, the
remainders are $R$ and $R'$, respectively. When $PP'$ and $RR'$ are divided by $D$, the remainders
are $r$ and $r'$, respectively. Then $r = r'$ -/
theorem number_theory_95971 {P P' D R R' r r' : ℕ} (hR : R = P % D)
    (hR' : R' = P' % D) (hr : r = (P * P') % D) (hr' : r' = (R * R' % D)) :
    r = r' := by

  -- A number is modulo equivalent to its remainder, so we have $P = R \operatorname{mod} D$ and
  -- $P' = R' \operatorname{mod} D$.
  have hPR : P ≡ R [MOD D] := by
    rw [hR]
    exact Nat.ModEq.symm (Nat.mod_modEq P D)
  have hP'R' : P' ≡ R' [MOD D] := by
    rw [hR']
    exact Nat.ModEq.symm (Nat.mod_modEq P' D)

  -- Multiplying congruent numbers leads to congruent products, so we have
  -- $PP' = RR' \operatorname{mod} D$.
  have : (P * P') ≡ (R * R') [MOD D] := by
    exact Nat.ModEq.mul hPR hP'R'

  -- Thus $P P'$ and $R R'$ have the same remainder when divided by $D$, so $r = r'$.
  rw [hr, hr']
  exact this