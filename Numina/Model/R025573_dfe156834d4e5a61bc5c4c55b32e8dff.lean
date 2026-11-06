import Mathlib

def is_convenient (n : ℕ) := 1000001 ∣ (n ^ 2 + 1)

theorem number_theory_199852 :
    Even {n | n ∈ Finset.Icc 1 1000000 ∧ is_convenient n}.ncard := by
  have h1 : {n | n ∈ Finset.Icc 1 1000000 ∧ is_convenient n} = Finset.filter (fun n => 1000001 ∣ (n ^ 2 + 1)) (Finset.Icc 1 1000000) := by
    ext n
    simp [is_convenient]
  rw [h1] at *
  rw [Set.ncard_coe_Finset]
  native_decide