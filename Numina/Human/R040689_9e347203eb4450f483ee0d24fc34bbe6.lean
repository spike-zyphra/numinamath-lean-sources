import Mathlib

theorem number_theory_205203 :
    let S := fun (n : ℕ) => (Nat.digits 10 n).sum
    S (S (S (S (2017^2017)))) = 1 := by
  native_decide