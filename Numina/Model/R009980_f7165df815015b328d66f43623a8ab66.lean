import Mathlib

theorem number_theory_4462
(a r : ℝ)
(h₀ : r ≠ 1)
(n : ℕ) :
(∑ j in Finset.range (n + 1), a * r ^ j) = (a * r ^ (n + 1) - a) / (r - 1) := by
  induction n with
  | zero =>
    simp
    <;> field_simp [(show r - 1 ≠ 0 by intro hc; apply h₀; linarith)]
    <;> all_goals ring_nf
    <;> all_goals norm_num
    <;> all_goals tauto
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    field_simp [(show r - 1 ≠ 0 by intro hc; apply h₀; linarith)]
    <;> ring_nf
    <;> all_goals
      field_simp [(show r - 1 ≠ 0 by intro hc; apply h₀; linarith)]
      <;> ring_nf
      <;> all_goals
        field_simp [(show r - 1 ≠ 0 by intro hc; apply h₀; linarith)]
        <;> tauto