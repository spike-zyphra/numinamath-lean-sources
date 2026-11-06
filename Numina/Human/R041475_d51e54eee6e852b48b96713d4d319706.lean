import Mathlib

/- Let $a,b, c$ be $3$ distinct numbers from $\{1, 2,3, 4, 5, 6\}$
Show that $7$ divides $abc + (7 - a)(7 - b)(7 - c)$ -/
theorem number_theory_69524 (a b c : ℕ) (ha : a ∈ Finset.Icc 1 6)
    (hb : b ∈ Finset.Icc 1 6) (hc : c ∈ Finset.Icc 1 6) (hdist : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    7 ∣ a * b * c + (7 - a) * (7 - b) * (7 - c) := by
  fin_cases ha <;> fin_cases hb <;> fin_cases hc <;> norm_num <;> decide