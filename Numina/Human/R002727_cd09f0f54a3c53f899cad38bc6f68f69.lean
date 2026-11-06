import Mathlib

/-
Problem A2. Determine all four digit numbers $\overline{a b c d}$ such that

$$
a(a+b+c+d)\left(a^{2}+b^{2}+c^{2}+d^{2}\right)\left(a^{6}+2 b^{6}+3 c^{6}+4 d^{6}\right)=\overline{a b c d}
$$
 -/
theorem number_theory_104780 :
    {Nat.ofDigits 10 [d, c, b, a] | (a : ℕ) (b : ℕ) (c : ℕ) (d : ℕ) (_ : a ∈ Finset.Ico 1 10) (_ : b ∈ Finset.Ico 0 10) (_ : c ∈ Finset.Ico 0 10) (_ : d ∈ Finset.Ico 0 10) (_ : a * (a + b + c + d) * (a^2 + b^2 + c^2 + d^2) * (a^6 + 2 * b^6 + 3 * c^6 + 4 * d^6) = Nat.ofDigits 10 [d, c, b, a])} = {2010} := by
  -- We show that the only solution is 2010.
  ext x
  constructor
  . -- If abcd satisfies the condition
    -- We can check all the possible values of a, b, c, d.
    -- There are in total 9000 possible cases.
    -- We can use `native_decide` with `revert` to check each case.
    rintro ⟨a, b, c, d, ha, hb, hc, hd, h, rfl⟩
    revert d
    revert c
    revert b
    revert a
    native_decide
  . -- We check 2010 is ok.
    rintro rfl
    use 2, 0, 1, 0
    native_decide
