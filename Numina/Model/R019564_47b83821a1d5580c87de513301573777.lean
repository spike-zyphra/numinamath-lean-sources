import Mathlib

open Finset

/- An integer $x$ is randomly and equally likely generated from the set $\left\{ 1,2,\cdots ,2016 \right\}$. The probability that the sum of the digits of $x$ in binary representation does not exceed $8$ is ___          ___. -/
theorem number_theory_12367 :
    (Nat.card {x : ℕ | x ∈ Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8}) / 2016 = 655 / 672 := by 
  have h1 : Nat.card {x : ℕ | x ∈ Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8} = 1965 := by 
    have h2 : {x : ℕ | x ∈ Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8} = Finset.filter (fun (x : ℕ) => (Nat.digits 2 x).sum ≤ 8) (Icc 1 2016) := by 
      ext x 
      simp 
    rw [h2] 
    rw [Nat.card_eq_fintype_card] 
    native_decide 
  calc 
    (Nat.card {x : ℕ | x ∈ Icc 1 2016 ∧ (Nat.digits 2 x).sum ≤ 8}) / 2016 = 1965 / 2016 := by 
      rw [h1] 
    _ = 655 / 672 := by 
      norm_num