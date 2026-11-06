import Mathlib

/- Find all the three digit numbers $\overline{a b c}$ such that

$$
\overline{a b c}=a b c(a+b+c)
$$ -/
theorem number_theory_604373 (a b c : ℕ) (ha : a ≠ 0) (au: a ≤ 9) (bu: b ≤ 9) (cu: c ≤ 9):
  100 * a + 10 * b + c = a * b * c * (a + b + c) ↔ a = 1 ∧ b = 3 ∧ c = 5 ∨ a = 1 ∧ b = 4 ∧ c = 4 := by 

  constructor
  intro h
  
  --From left to right, simple checking.
  interval_cases a <;>
  interval_cases b <;>
  interval_cases c <;>
  simp at ha h ⊢

  --From right to left, we verify that both numbers are valid.
  intro h
  obtain ⟨ae,be,ce⟩ | ⟨ae,be,ce⟩ := h <;>
  simp [ae,be,ce]