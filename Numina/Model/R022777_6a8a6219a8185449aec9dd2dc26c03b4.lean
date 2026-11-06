import Mathlib

theorem number_theory_114999 :
    Set.Infinite {x : Fin 10 → ℤ | ∑ i : Fin 10, x i ^ 3 = 600} := by 
  apply Set.infinite_of_injective_forall_mem (f := fun (n : ℕ) => (λ (i : Fin 10) => 
    match i.val with 
      | 0 => 8 
      | 1 => 3 
      | 2 => 3 
      | 3 => 3 
      | 4 => 2 
      | 5 => -1 
      | 6 => (n : ℤ) 
      | 7 => -(n : ℤ) 
      | 8 => 0 
      | 9 => 0 
      | _ => 0
  )
)
  · -- Show f is injective.
    intro n m h
    simp [funext_iff] at h 
    have h6 := h 6
    simp at h6 
    omega
  · -- Show that each element of the sequence is in the set.
    intro n 
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
    <;> ring_nf <;> norm_num 
    <;> ring_nf <;> norm_num
    all_goals try { simp [funext_iff] }
    all_goals try { ring }