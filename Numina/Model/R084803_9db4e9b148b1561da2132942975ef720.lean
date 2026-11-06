import Mathlib

theorem number_theory_232830 (a b : ℕ) (ha : a ∈ Finset.Icc 100 999) (hb : b ∈ Finset.Icc 10 99) :
    a + b ≥ 110 ∧ a + b ≤ 1098 ∧ a - b ≥ 1 ∧ a - b ≤ 989 := by
  rw [Finset.mem_Icc] at ha
  rw [Finset.mem_Icc] at hb
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  constructor
  · -- Proof that a + b ≥ 110
    omega
  constructor
  · -- Proof that a + b ≤ 1098
    omega
  constructor
  · -- Proof that a - b ≥ 1
    omega
  · -- Proof that a - b ≤ 989
    omega