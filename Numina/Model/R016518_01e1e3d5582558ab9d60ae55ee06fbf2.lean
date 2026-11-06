import Mathlib

theorem algebra_213981 {a b c : ℝ} (h : a ≠ b ∧ a ≠ c ∧ b ≠ c) :
    (a ^ 0 / ((a - b) * (a - c)) + b ^ 0 / ((b - a) * (b - c)) +
     c ^ 0 / ((c - a) * (c - b))) = 0 ∧
    (a ^ 1 / ((a - b) * (a - c)) + b ^ 1 / ((b - a) * (b - c)) +
     c ^ 1 / ((c - a) * (c - b))) = 0 ∧
    (a ^ 2 / ((a - b) * (a - c)) + b ^ 2 / ((b - a) * (b - c)) +
     c ^ 2 / ((c - a) * (c - b))) = 1 ∧
    (a ^ 3 / ((a - b) * (a - c)) + b ^ 3 / ((b - a) * (b - c)) +
     c ^ 3 / ((c - a) * (c - b))) = a + b + c := by

  have hab : a - b ≠ 0 := by
    intro h1
    apply h.1
    linarith

  have hac : a - c ≠ 0 := by
    intro h1
    apply h.2.1
    linarith

  have hba : b - a ≠ 0 := by
    intro h1
    apply h.1
    linarith

  have hbc : b - c ≠ 0 := by
    intro h1
    apply h.2.2
    linarith

  have hca : c - a ≠ 0 := by
    intro h1
    apply h.2.1
    linarith

  have hcb : c - b ≠ 0 := by
    intro h1
    apply h.2.2
    linarith

  constructor
  · -- Show $S_0 = 0$
    field_simp [hab, hac, hba, hbc, hca, hcb]
    <;> ring
  constructor
  · -- Show $S_1 = 0$
    field_simp [hab, hac, hba, hbc, hca, hcb]
    <;> ring
  constructor
  · -- Show $S_2 = 1$
    field_simp [hab, hac, hba, hbc, hca, hcb]
    <;> ring_nf
    <;> field_simp
    <;> ring
  · -- Show $S_3 = a + b + c$
    field_simp [hab, hac, hba, hbc, hca, hcb]
    <;> ring_nf
    <;> field_simp
    <;> ring