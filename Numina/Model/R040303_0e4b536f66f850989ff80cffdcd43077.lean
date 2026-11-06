import Mathlib

theorem number_theory_294420 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ a b c, a = (n / 100) % 10 ∧ b = (n % 100) / 10 ∧ c = n % 10 ∧ a + c = 2 * b} = 45 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ a b c, a = (n / 100) % 10 ∧ b = (n % 100) / 10 ∧ c = n % 10 ∧ a + c = 2 * b} = Finset.filter (fun n => 
      let a := (n / 100) % 10
      let b := (n % 100) / 10
      let c := n % 10
      a + c = 2 * b
    ) (Finset.Icc 100 999) := by
    ext n
    simp
    <;> aesop
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide