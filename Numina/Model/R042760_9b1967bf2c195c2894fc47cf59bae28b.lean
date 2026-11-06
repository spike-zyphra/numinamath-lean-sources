import Mathlib

theorem algebra_297822 {p q : ℤ} (h : p ≠ 0) (h1 : 1997^2 + p * 1997 + q = 0) (h2 : 1998^2 + p * 1998 + q = 0)
    (y : ℕ → ℤ) (hy : ∀ x, y x = x^2 + p * x + q) :
    Set.ncard {x | 6 ∣ y x ∧ 0 ≤ x ∧ x ≤ 1999} = 1333 := by

  have hp : p = -3995 := by
    nlinarith
  have hq : q = 1997 * 1998 := by
    rw [hp] at h1
    nlinarith

  have : {x | 6 ∣ y x ∧ 0 ≤ x ∧ x ≤ 1999} = Finset.filter (fun x => 6 ∣ y x ∧ 0 ≤ x ∧ x ≤ 1999) (Finset.Icc (0 : ℕ) 1999) := by
    ext x
    simp
    <;> omega

  rw [this]
  rw [Set.ncard_coe_Finset]

  simp [hy, hp, hq]
  <;> native_decide