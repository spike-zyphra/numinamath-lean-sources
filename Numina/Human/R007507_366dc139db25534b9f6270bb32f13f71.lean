import Mathlib

/- Example 2 Let $p$ be a prime. Prove: $\mathrm{C}_{n}^{p} \equiv\left[\frac{n}{p}\right]$ $(\bmod p)$ -/
theorem number_theory_202717 (n p : ℕ) (hp : Nat.Prime p) :
    Nat.choose n p ≡ n / p [MOD p] := by
  -- Mathlib already has the following lemma:
  -- n.choose k ≡ (n % p).choose (k % p) * (n / p).choose (k / p) [MOD p].
  -- Apply this lemma with k = p and get n.choose k ≡ 1 * (n / p).choose (p / p) [MOD p].
  apply Nat.ModEq.trans (@Choose.choose_modEq_choose_mod_mul_choose_div_nat n p p ⟨hp⟩)
  -- It is left to show that p / p = 1. The result follows from 0 < p for any prime p.
  simp [Nat.div_self hp.pos]
  rfl