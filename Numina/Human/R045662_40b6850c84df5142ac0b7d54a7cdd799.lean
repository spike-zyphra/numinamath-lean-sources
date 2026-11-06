import Mathlib
open Real
/- Evaluate
$$
\sum_{k=1}^{2010} \cos ^{2}(k)
$$ -/
theorem algebra_608718 : ∑ i ∈ Finset.range 2010, cos (i + 1) ^ 2 = 1005 + (sin 4021 - sin 1) / (4 * sin 1):= by
  -- Set m as 2010 for easier manipulation
  set m:= 2010 with hm
  clear_value m

  -- Use the double angle formula: cos²(x) = 1/2 + cos(2x)/2
  have h1 : ∀ i ∈ Finset.range m, cos (i + 1) ^ 2 = 1 / 2 + cos (2 * (i + 1)) / 2:= by
    intro i _
    have h2:= cos_two_mul (i + 1)
    linarith

  -- Apply the formula to the sum
  have h2 : ∑ i ∈ Finset.range m, cos (i + 1) ^ 2 = ∑ i ∈ Finset.range m, (1 / 2 + cos (2 * (i + 1)) / 2):= by exact Finset.sum_congr rfl h1
  rw [h2]

  -- Split the sum into two parts: sum of 1/2 and sum of cos(2(i+1))/2
  have h3 : ∑ i ∈ Finset.range m, (1 / 2 + cos (2 * (i + 1)) / 2) = ∑ i ∈ Finset.range m, (1 / 2) + ∑ i ∈ Finset.range m, (cos (2 * (i + 1)) / 2):= by exact Finset.sum_add_distrib
  rw [h3]
  simp

  -- Prove by induction that the sum of cos(2(i+1))/2 equals (sin(2n+1) - sin(1))/(4sin(1))
  have h4 : ∀ n : ℕ, ∑ i ∈ Finset.range n, cos (2 * (i + 1)) / 2 = (sin (2 * n + 1) - sin 1) / (4 * sin 1):= by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      -- Inductive step using trigonometric identities
      rw [Finset.sum_range_succ, ih]
      -- Prove sin(1) > 0 for division
      have g1 : sin 1 > 0:= by refine sin_pos_of_pos_of_le_two (by linarith) (by linarith)
      rw [show (2 : ℝ) * (↑n + 1) = 2 * ↑n + 1 + 1 by linarith]
      rw [show cos (2 * ↑n + 1 + 1) = sin 1 * cos (2 * ↑n + 1 + 1) / sin 1 by field_simp]
      -- Apply sine addition and subtraction formulas
      have g2:= Real.sin_sub 1 (2 * ↑n + 1 + 1)
      have g3:=Real.sin_add 1 (2 * ↑n + 1 + 1)
      rw [show (1 : ℝ) - (2 * ↑n + 1 + 1) = - (2 * ↑n + 1) by ring] at g2
      rw [show (1 : ℝ) + (2 * ↑n + 1 + 1) = 2 * ↑n + 3 by ring] at g3
      rw [show sin (-(2 * (↑n : ℝ) + 1)) = - sin (2 * ↑n + 1) by exact sin_neg (2 * (↑n : ℝ) + 1)] at g2
      rw [show sin 1 * cos (2 * ↑n + 1 + 1) = (sin (2 * ↑n + 3) - sin (2 * ↑n + 1)) / 2 by linarith]
      clear g2 g3
      simp
      rw [show 2 * (↑n + 1) + (1 : ℝ) = 2 * ↑n + 3 by ring]
      field_simp
      linarith

  -- Apply the formula with m = 2010 and simplify
  rw [h4 m]
  subst m
  ring_nf
