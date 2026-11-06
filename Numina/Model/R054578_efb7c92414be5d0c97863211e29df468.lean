import Mathlib

def is_five_star (n : ℕ) := (Nat.digits 10 n).sum ≡ 0 [MOD 5]

theorem number_theory_119931 : {n | 1 ≤ n ∧ n ≤ 2022 ∧ is_five_star n}.encard = 404 := by
  have h1 : {n | 1 ≤ n ∧ n ≤ 2022 ∧ is_five_star n} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2022 ∧ (Nat.digits 10 n).sum ≡ 0 [MOD 5]) (Finset.Icc (0 : ℕ) 2022) := by
    ext n
    simp [is_five_star]
    omega
  rw [h1]
  rw [Finset.filter]
  simp [Finset.Icc, is_five_star, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }
  <;> try { aesop }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { tauto }
  <;> try { native_decide }
  all_goals try { native_decide }
  all_goals try { native_decide }