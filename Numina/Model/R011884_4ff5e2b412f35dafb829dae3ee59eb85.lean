import Mathlib

open Finset

theorem number_theory_61041 {f g : ℕ → ℤ}
    (hf : ∀ n, f n = ∑ d ∈ Icc 1 n, n / d)
    (hg : ∀ n, g n = f n - f (n - 1)) :
    {n | n ∈ Icc 1 100 ∧ Even (g n)}.ncard = 90 := by
  have h1 : {n | n ∈ Icc 1 100 ∧ Even (g n)} = Finset.filter (fun n => Even (g n)) (Icc 1 100) := by
    ext n
    simp
    <;> tauto 
  rw [h1]
  rw [Set.ncard_coe_Finset]
  simp [hg, hf]
  <;> native_decide