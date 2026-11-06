import Mathlib

def is_palindrome (n : ℕ) := Nat.digits 10 n = List.reverse (Nat.digits 10 n)

theorem number_theory_114482 :
    (∃ n, n ∈ Finset.Icc 10000 99999 ∧ is_palindrome n ∧ 5 ∣ n) ∧
    {n | n ∈ Finset.Icc 10000 99999 ∧ is_palindrome n ∧ 5 ∣ n}.ncard = 100 := by 
  constructor
  · -- Show the existence of a five-digit palindromic number divisible by 5
    use 51715
    constructor
    · -- Show 51715 is in the range [10000, 99999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    constructor
    · -- Show 51715 is a palindrome 
      unfold is_palindrome
      norm_num
    · -- Show 51715 is divisible by 5 
      norm_num 
  · -- Show that the cardinality of the set is 100 
    have h1 : {n | n ∈ Finset.Icc 10000 99999 ∧ is_palindrome n ∧ 5 ∣ n} = Finset.filter (fun n : ℕ => 
      Nat.digits 10 n = List.reverse (Nat.digits 10 n) ∧ 5 ∣ n) (Finset.Icc 10000 99999) := by 
      ext n 
      simp [is_palindrome]
    rw [h1] 
    rw [Set.ncard_coe_Finset] 
    native_decide