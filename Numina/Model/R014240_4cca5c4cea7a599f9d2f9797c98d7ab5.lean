import Mathlib

def is_n_primable (n : ℕ) (k : ℕ) : Prop :=
  n ∣ k ∧ ∀ d ∈ Nat.digits 10 k, Nat.Prime d ∧ d < 10

theorem number_theory_2658 :
    Set.ncard {k | 0 < k ∧ k < 1000 ∧ is_n_primable 3 k} = 28 := by
  have h1 : {k | 0 < k ∧ k < 1000 ∧ is_n_primable 3 k} = Finset.filter (fun k => 0 < k ∧ k < 1000 ∧ (3 ∣ k ∧ ∀ d ∈ Nat.digits 10 k, Nat.Prime d ∧ d < 10)) (Finset.Icc 0 999) := by
    ext k
    simp [is_n_primable]
    <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide