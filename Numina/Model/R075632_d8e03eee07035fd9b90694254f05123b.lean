import Mathlib

/- If $a$, $b$ are natural numbers, and $a>b$, $2011=a(a-1)+b$. Then $a=$ ___          ___ ; $b=$ ___          ___. -/
theorem number_theory_1237
    {a b : ℕ} (hab : a > b) (h : 2011 = a * (a - 1) + b) :
    a = 45 ∧ b = 31 := by
  have h1 : a ≤ 45 := by
    by_contra h1
    push_neg at h1
    have h2 : a ≥ 46 := by omega
    have h3 : a * (a - 1) ≥ 2070 := by
      have h4 : a - 1 ≥ 45 := by omega
      nlinarith [h2, h4]
    omega -- handles the contradiction
  interval_cases a <;> omega
  <;> try { tauto }
  <;> try { omega }