import Mathlib

def is_triangular (a b c d : ℕ) : Prop :=
  a + b > c ∧ a + c > b ∧ b + c > a ∧
  a + d > b ∧ a + b > d ∧ b + d > a ∧
  b + c > d ∧ b + d > c ∧ c + d > b ∧
  c + d > a ∧ c + a > d ∧ d + a > c

theorem number_theory_327493 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ is_triangular (n / 1000) (n % 1000 / 100) (n % 1000 % 100 / 10) (n % 10)} = 1681 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ is_triangular (n / 1000) (n % 1000 / 100) (n % 1000 % 100 / 10) (n % 10)} = Finset.filter (fun n => 
    let a := n / 1000
    let b := n % 1000 / 100
    let c := n % 1000 % 100 / 10
    let d := n % 10
    a + b > c ∧ a + c > b ∧ b + c > a ∧
    a + d > b ∧ a + b > d ∧ b + d > a ∧
    b + c > d ∧ b + d > c ∧ c + d > b ∧
    c + d > a ∧ c + a > d ∧ d + a > c
  ) (Finset.Icc 1000 9999) := by
    ext n
    simp [is_triangular]
    <;> tauto
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide