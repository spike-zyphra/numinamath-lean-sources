import Mathlib
open Real
theorem algebra_608718 : ∑ i ∈ Finset.range 2010, cos (i + 1) ^ 2 = 1005 + (sin 4021 - sin 1) / (4 * sin 1):= by
  have h1 : ∀ i ∈ Finset.range 2010, cos (i + 1) ^ 2 = 1 / 2 + cos (2 * (i + 1)) / 2:= by
    intro i _
    have h2:= cos_two_mul (i + 1)
    linarith

  have h2 : ∑ i ∈ Finset.range 2010, cos (i + 1) ^ 2 = ∑ i ∈ Finset.range 2010, (1 / 2 + cos (2 * (i + 1)) / 2):= by exact Finset.sum_congr rfl h1
  rw [h2]

  have h3 : ∑ i ∈ Finset.range 2010, (1 / 2 + cos (2 * (i + 1)) / 2) = ∑ i ∈ Finset.range 2010, (1 / 2) + ∑ i ∈ Finset.range 2010, (cos (2 * (i + 1)) / 2):= by exact Finset.sum_add_distrib
  rw [h3]
  simp

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
      field_simp
      ring_nf
      <;> simp [g1]
      <;> ring_nf <;> simp [Real.sin_add, Real.cos_add] <;> ring

  have h5 : ∑ i ∈ Finset.range 2010, cos (2 * (i + 1)) / 2 = (sin 4021 - sin 1) / (4 * sin 1):= by
    specialize h4 2010
    norm_num [h4] at *
    <;> ring_nf <;> simp [Real.sin_add, Real.cos_add] <;> ring
  linarith [h5]