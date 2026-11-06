import Mathlib

def f (n : ℕ) := (Nat.digits 2 n).sum

theorem number_theory_186686 :
    Set.ncard {n | 1 ≤ n ∧ n ≤ 2002 ∧ f n = f (n + 1)} = 501 := by

  have : {n | 1 ≤ n ∧ n ≤ 2002 ∧ f n = f (n + 1)} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2002 ∧ f n = f (n + 1)) (Finset.Icc 0 2002) := by
    ext n
    simp
    omega

  rw [this]
  rw [Set.ncard_coe_Finset]
  native_decide