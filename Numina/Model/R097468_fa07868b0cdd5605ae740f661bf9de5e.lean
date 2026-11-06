import Mathlib

def is_palindrome (n : ℕ) : Prop := Nat.digits 10 n = List.reverse (Nat.digits 10 n)

theorem number_theory_9968 :
    ∑ᶠ n ∈ {n | n ∈ Finset.Icc 1000 9999 ∧ is_palindrome n}, n = 495000 := by
  have h1 : {n | n ∈ Finset.Icc 1000 9999 ∧ is_palindrome n} = Finset.filter (fun n => Nat.digits 10 n = List.reverse (Nat.digits 10 n)) (Finset.Icc 1000 9999) := by
    ext n
    simp [is_palindrome]
    <;> tauto
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide