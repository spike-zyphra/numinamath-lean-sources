import Mathlib

theorem number_theory_10645 {isGood : ℕ → Prop}
    (hg : ∀n, isGood n = (n ∈ Finset.Icc 10 99 ∧ n / 10 > 0 ∧ n % 10 > 0 ∧ Nat.gcd n (Nat.ofDigits 10 (Nat.digits 10 n).reverse) > 1)) :
    Set.ncard {n | isGood n} = 41 := by
  have h1 : {n | isGood n} = Finset.filter (fun n => 
    n / 10 > 0 ∧ n % 10 > 0 ∧ Nat.gcd n (Nat.ofDigits 10 (Nat.digits 10 n).reverse) > 1) (Finset.Icc 10 99) := by
    ext n
    simp [hg]
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide