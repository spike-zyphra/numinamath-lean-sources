import Mathlib

/- A natural number is a *factorion* if it is the sum of the factorials of each of its decimal digits. For example,  $145$  is a factorion because  $145 = 1! + 4! + 5!$ .
Find every 3-digit number which is a factorion.-/
theorem number_theory_8507 :
    {n : ℕ | n ∈ Finset.Ico 100 1000 ∧ n = ((Nat.digits 10 n).map Nat.factorial).sum} = {145} := by
  ext n
  simp
  constructor
  swap
  -- Verify that 145=1!+4!+5!
  . intro h
    subst h
    norm_num
    native_decide
  rintro ⟨⟨hn1, hn2⟩, hn⟩
  rw [Nat.digits_def' (by norm_num) (by omega),
    Nat.digits_def' (by norm_num) (by omega),
    Nat.digits_def' (by norm_num) (by omega),
    show n / 10 / 10 / 10 = 0 by omega] at hn
  simp at hn
  interval_cases n
  pick_goal 46
  . norm_num
  -- Checking that 3-digit number other than 145 did not satify abc=a!+b!+c!.
  all_goals contrapose! hn; native_decide
