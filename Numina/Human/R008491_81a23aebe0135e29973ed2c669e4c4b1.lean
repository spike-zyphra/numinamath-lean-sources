import Mathlib

/- Eleanor is making chocolate chip cookies for her friends. If she divides the cookies equally among $11$ of her friends, she'll have $4$ cookies left over. If she divides the cookies equally among $7$ of her friends, she'll have $1$ cookie left over. Assuming that Eleanor made fewer than $100$ cookies, what is the sum of the possible numbers of cookies that she could have made? -/
theorem number_theory_14824 (s : Finset ℕ) (hs : s = {n ∈ Finset.range 100 | n % 11 = 4 ∧ n % 7 = 1}) : ∑x in s, x = 107 := by
  -- proof of ${x | x < 100 \and n%11=4 \and n%7=1} = {15, 92}$
  have heq : s = {15, 92} := by
    ext x
    rw [hs]
    constructor
    . -- proof of of $x < 100 ∧ n%11=4 ∧ n%7=1 → x ∈ {15, 92}$
      intro h
      -- we direct iterate 0 to 100, we find only 15 and 92 satisfy equation
      fin_cases h
      repeat simp
    . -- proof of of $x ∈ {15, 92} → $x < 100 ∧ n%11=4 ∧ n%7=1$
      intro hx
      simp
      fin_cases hx
      repeat simp
  rw [heq]
  simp
