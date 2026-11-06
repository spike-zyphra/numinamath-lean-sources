import Mathlib

/-Let $\overline{abcd}$ be a four-digit number,
where $a,b,c,d$ are its decimal digits with $a \neq 0$.
Let $\overline{dcba}$ denote the number formed by reversing the digits of $\overline{abcd}$.
If $\overline{abcd} = 4 \cdot \overline{dcba}$, show that $\overline{abcd}=8712$.-/

theorem number_theory_640025 (a b c d: ℤ) (h: 1 ≤ a ∧ a ≤ 9 ∧ 0 ≤ b ∧ b ≤ 9 ∧ 0 ≤ c ∧ c ≤ 9 ∧ 0 ≤ d ∧ d ≤ 9 ∧
  a * 1000 + b * 100 + c * 10 + d = 4 * (d * 1000 + c * 100 + b * 10 + a)): a = 8 ∧ b = 7 ∧ c = 1 ∧ d = 2 := by

  rcases h with ⟨ha1, ha2, hb1, hb2, hc1, hc2, hd1, hd2, h⟩

  -- we show that d < 3
  have ld: d < 3 := by
    nlinarith

  interval_cases d

  -- d = 0
  .
    simp at h
    have la: a < 3 := by
      omega
    interval_cases a
    .
      simp at h
      omega
    .
      simp at h
      omega

  -- d = 1
  .
    simp at h
    have la: 3 ≤ a := by
      omega
    have ra: a < 7 := by
      omega
    interval_cases a
    all_goals omega

  -- d = 2
  .
    simp at h
    have la: 7 ≤ a := by
      omega
    have ra: a < 9 := by
      omega
    interval_cases a
    all_goals omega