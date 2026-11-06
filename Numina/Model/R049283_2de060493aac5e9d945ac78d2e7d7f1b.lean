import Mathlib

theorem number_theory_14756 : {n | Even n ∧ n ∈ Nat.digits 7 (403)}.encard = 1 := by
  have h1 : Nat.digits 7 403 = [4, 1, 1, 1] := by
    norm_num [Nat.digits, Nat.digitsAux]
  have h2 : {n | Even n ∧ n ∈ Nat.digits 7 403} = {4} := by
    ext n
    simp [h1, Nat.even_iff]
    <;> omega
  rw [h2]
  rw [Set.encard]
  simp
  <;> try { native_decide }
  <;> try { omega }
  <;> try { norm_num }
  <;> try { native_decide }
  <;> try { omega }
  <;> try { tauto }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }