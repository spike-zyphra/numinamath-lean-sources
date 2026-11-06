import Mathlib

def f (x : ℕ) := 2 ^ x + 3 ^ x

theorem number_theory_64357 :
    Set.ncard {n | 1 ≤ n ∧ n ≤ 2020 ∧ ∀ k < n, Nat.Coprime (f n) (f k)} = 11 := by
  have h1 : {n | 1 ≤ n ∧ n ≤ 2020 ∧ ∀ k < n, Nat.Coprime (f n) (f k)} = 
          Finset.filter (fun n => 1 ≤ n ∧ n ≤ 2020 ∧ ∀ k < n, Nat.Coprime (f n) (f k)) (Finset.Icc (0 : ℕ) 2020) := by 
    ext n
    simp
    <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide