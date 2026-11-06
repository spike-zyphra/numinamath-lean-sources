import Mathlib

/- What is the largest negative integer $x$ satisfying $$24x \equiv 15 \pmod{1199}~?$$ -/
theorem number_theory_19339 : IsGreatest {x | x < 0 ∧ 24 * x ≡ 15 [ZMOD 1199]} (-449) := by
  constructor
  -- $-449$ is a possible value
  simp only [Int.reduceNeg, Set.mem_setOf_eq, Left.neg_neg_iff, Nat.ofNat_pos, mul_neg, Int.reduceMul, true_and]
  exact rfl
  -- $-449$ is the greatest such value
  intro x xin
  rcases xin with ⟨xneg, xmod⟩
  apply Int.ModEq.mul_left 50 at xmod
  -- To solve the congruence $24x\equiv 15\pmod{1199}$, we multiply both sides by $50$ and simplify: \begin{align*} 50\cdot 24x &\equiv 50\cdot 15 \pmod{1199} \\ x &\equiv 750 \pmod{1199} \end{align*}
  have mod1 : 50 * (24 * x) ≡ x [ZMOD 1199] := by
    refine Int.ModEq.symm ((fun {a b n} => Int.modEq_iff_add_fac.mpr) ?_)
    use x
    ring
  have mod2 : x ≡ 50 * 15 [ZMOD 1199] := by
    exact Int.ModEq.trans (id (Int.ModEq.symm mod1)) xmod
  apply Int.ModEq.dvd at mod2
  rcases mod2 with ⟨k, hk⟩
  -- The largest negative solution is $750-1199 = \boxed{-449}$
  have kge : 1 ≤ k := by
    by_contra contra
    rw [not_le] at contra
    have xeq : x = 50 * 15 - 1199 * k := by
      linarith
    have xge : x ≥ 50 * 15 - 1199 * 0 := by
      rw [xeq]
      linarith
    norm_num at xge
    linarith
  linarith
