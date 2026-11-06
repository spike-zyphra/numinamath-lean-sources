import Mathlib

open Finset

theorem number_theory_55584 (S : Finset (ℤ × ℤ))
    (hS : ∀ a b : ℤ, (a, b) ∈ S ↔ 0 < 2 * a ∧ 2 * a < 2 * b ∧ 2 * b < 2017 ∧ 2017 ∣ a ^ 2 + b ^ 2) :
    ∑ a in S, a.1 = (∑ a in S, a.2) / 2 := by
  have h1 : S = Finset.filter (fun s : ℤ × ℤ => 
    0 < 2 * s.1 ∧ 2 * s.1 < 2 * s.2 ∧ 2 * s.2 < 2017 ∧ 2017 ∣ s.1 ^ 2 + s.2 ^ 2) (Finset.Icc (-999 : ℤ) 1008 ×ˢ Finset.Icc (-999 : ℤ) 1008) := by
    ext ⟨a, b⟩
    simp [hS]
    <;> omega
  rw [h1]
  native_decide