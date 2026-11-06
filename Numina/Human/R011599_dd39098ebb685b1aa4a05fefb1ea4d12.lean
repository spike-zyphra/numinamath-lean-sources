import Mathlib

/-
Determine all solutions of the equation

$$
a^{2}=b \cdot(b+7)
$$

with integers $a \geq 0$ and $b \geq 0$.

W. Janous, WRG Ursulinen, Innsbruck
-/

theorem number_theory_259171 (a b : ℤ) (ha: 0 ≤ a) (hb: 0 ≤ b):
a^2 = b * (b+7) ↔ (a=0 ∧ b=0) ∨ (a=12 ∧ b=9) := by

  constructor

  --From left to right. Since a^2 = b * (b+7), we have a = b, or b + 1, or b + 2, or b + 3.
  intro h
  have : b ≤ a := by 
    by_contra
    have : a < b := by omega
    have : a^2 < b^2 := by nlinarith
    linarith
  have : a < b + 4 := by
    by_contra
    have : b + 4 ≤ a := by omega
    have : b * (b + 7) < a^2 := by nlinarith
    linarith

  --We check each case separately.
  by_cases aeb : a = b
  rw [aeb] at h
  ring_nf at h
  field_simp at h
  left
  omega
  by_cases aeb1: a = b + 1
  rw [aeb1] at h
  ring_nf at h
  field_simp at h
  exfalso
  omega
  by_cases aeb2: a = b + 2
  rw [aeb2] at h
  ring_nf at h
  field_simp at h
  exfalso
  omega
  have aeb3: a = b + 3 := by omega
  right
  rw [aeb3] at h
  ring_nf at h
  field_simp at h
  omega

  --From right to left. Simple verification.
  intro h
  rcases h with ⟨ae,be⟩ | ⟨ae,be⟩
  rw [ae,be];
  simp
  rw [ae,be]
  simp
