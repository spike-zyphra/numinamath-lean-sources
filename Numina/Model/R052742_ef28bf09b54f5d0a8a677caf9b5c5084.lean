import Mathlib

def isConvenient (n : ℕ) := 1000001 ∣ n^2 + 1

theorem number_theory_203300 :
    Even {n | 1 ≤ n ∧ n ≤ 1000000 ∧ isConvenient n}.ncard := by
  have h1 : {n | 1 ≤ n ∧ n ≤ 1000000 ∧ isConvenient n} = Finset.filter (fun n => 1 ≤ n ∧ n ≤ 1000000 ∧ 1000001 ∣ n^2 + 1) (Finset.Icc 0 1000000) := by
      ext n
      simp [isConvenient, Finset.mem_Icc]
      <;> omega

  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide