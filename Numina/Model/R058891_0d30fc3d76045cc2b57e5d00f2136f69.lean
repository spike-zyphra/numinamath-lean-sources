import Mathlib

theorem number_theory_263418 {N : ℕ} (hN : Odd N) (hN1 : N ∈ Finset.Ioo 400 600)
    (hN2 : 5 ∣ N) (hN3 : 11 ∣ N) :
    (Nat.digits 10 N).sum = 18 := by
  rw [Finset.mem_Ioo] at hN1
  rcases hN1 with ⟨hN11, hN12⟩
  have h4 : N = 495 := by
    interval_cases N <;> norm_num at hN2 hN3 hN11 hN12 ⊢ <;> try { trivial }
    <;> norm_num [Nat.odd_iff] at hN ⊢ <;> try { trivial }
    <;> try { try { trivial } <;> try { tauto } }
  rw [h4]
  norm_num