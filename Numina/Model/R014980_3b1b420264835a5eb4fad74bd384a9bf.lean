import Mathlib

def isSunny (n : ℕ) : Prop :=
  n ∈ Finset.Icc 1000 9999 ∧ (n / 1000) % 10 = (n / 100) % 10 + 1 ∧
    (n % 100) % 10 = (n / 10) % 10 + 1

theorem number_theory_171230 :
    {n | 0 < n ∧ isSunny n ∧ isSunny (2 * n)}.encard = 16 := by
  have h1 : {n | 0 < n ∧ isSunny n ∧ isSunny (2 * n)} = Finset.filter (fun n => 0 < n ∧
    (n ∈ Finset.Icc 1000 9999 ∧ (n / 1000) % 10 = (n / 100) % 10 + 1 ∧
    (n % 100) % 10 = (n / 10) % 10 + 1) ∧ 
    (2 * n ∈ Finset.Icc 1000 9999 ∧ (2 * n / 1000) % 10 = (2 * n / 100) % 10 + 1 ∧
    (2 * n % 100) % 10 = (2 * n / 10) % 10 + 1)
  ) (Finset.Icc 0 9999) := by
    ext n
    simp [isSunny]
    omega
  rw [h1]
  rw [Set.encard_coe_eq_coe_finsetCard]
  native_decide