import Mathlib

theorem algebra_21608 (a b : ℕ) (ha : a = 7) (hb : b = 13) :
    {x | 0 < x ∧ x < a * b ∧ Even x}.encard = 45 := by 
  rw [ha, hb]
  have h1 : {x | 0 < x ∧ x < 7 * 13 ∧ Even x} = Finset.filter (fun x => 0 < x ∧ x < 7 * 13 ∧ Even x) (Finset.Icc 0 (7 * 13 - 1)) := by
    ext x
    simp [Nat.even_iff]
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Nat.even_iff]
  <;> try { native_decide }