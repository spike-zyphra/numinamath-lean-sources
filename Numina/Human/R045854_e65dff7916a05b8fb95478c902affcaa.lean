import Mathlib

open Nat Finset

theorem number_theory_4494 :
    (IsLeast {n | 2 ≤ n ∧ ∀ i ∈ range 5, ¬ (n + i).Prime} 24) ∧ ∃ n, 2 ≤ n ∧ ∀ i ∈ range 1000000, ¬ (n + i).Prime := by
  constructor
  . constructor
    . simp
      native_decide
    . intro n ⟨hn, hn'⟩
      contrapose! hn'
      suffices H : ∀ n ∈ Ico 2 24, ∃ i ∈ range 5, (n + i).Prime from H n (mem_Ico.mpr ⟨hn, hn'⟩)
      native_decide
  . set m := 1000000 with hm
    refine ⟨(m + 1)! + 2, by simp, fun i hi => ?_⟩
    simp at hi
    rw [not_prime_iff_exists_dvd_lt (by omega)]
    refine ⟨2 + i, ?_, by simp, by linarith only [factorial_pos (m + 1)]⟩
    simp [add_assoc]
    exact dvd_factorial (by simp) (by omega)
