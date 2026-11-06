import Mathlib

theorem number_theory_267799 (m : ℕ) (hm : m = 500) :
    Set.ncard {n : ℕ | 1 ≤ n ∧ n ≤ 499 ∧ 1 ≤ m % n ∧ m % n ≤ 15 ∧ 2 ≤ n % (m % n) ∧ n % (m % n) ≤ 9 ∧ (m % n) % (n % (m % n)) = 0} = 13 := by
  rw [hm]
  have h₁ : {n : ℕ | 1 ≤ n ∧ n ≤ 499 ∧ 1 ≤ 500 % n ∧ 500 % n ≤ 15 ∧ 2 ≤ n % (500 % n) ∧ n % (500 % n) ≤ 9 ∧ (500 % n) % (n % (500 % n)) = 0} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 499 ∧ 1 ≤ 500 % n ∧ 500 % n ≤ 15 ∧ 2 ≤ n % (500 % n) ∧ n % (500 % n) ≤ 9 ∧ (500 % n) % (n % (500 % n)) = 0) (Finset.Icc 0 499) := by
    ext n
    simp
    <;> omega
  rw [h₁]
  rw [Set.ncard_coe_Finset]
  native_decide