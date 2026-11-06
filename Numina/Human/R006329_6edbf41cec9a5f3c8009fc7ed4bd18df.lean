import Mathlib

/- Let $k$ be an integer. Show that for any integer $n$, the fractions $\frac{n-k}{15}$ and $\frac{n-(k+1)}{24}$ cannot both be integers. -/
theorem number_theory_635942 (k n : ℤ) :
    ¬(15 ∣ (n - k) ∧ 24 ∣ (n - (k + 1))) :=
by
  push_neg
  intro H1 H2
  rcases H1 with ⟨a, H1⟩
  rcases H2 with ⟨b, H2⟩
  have : 15 * a - 24 * b = 1 := by omega
  have : 1 = 3 * (5 * a - 8 * b) := by omega
  omega
