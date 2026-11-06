import Mathlib

theorem number_theory_3490 (A : Fin 10 → Bool) (hA : A = fun d : Fin 10 => 15 ∣ Nat.ofDigits 10 [5, 4, d, 4, d, 4]) : ∑ᶠ d ∈ {d : Fin 10 | A d}, d = 15 := by 
  rw [hA]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Finset.sum_insert, Finset.sum_singleton]
  <;> native_decide