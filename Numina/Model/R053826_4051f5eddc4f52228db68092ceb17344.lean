import Mathlib

theorem number_theory_9716 :
    ∑ᶠ x ∈ {x : ℤ | 2000 ≤ x ∧ x < 2023 ∧ (2 * x ^ 2 + 2 * x + 3) % 23 = 4}, x = 4024 := by
  have h1 : {x : ℤ | 2000 ≤ x ∧ x < 2023 ∧ (2 * x ^ 2 + 2 * x + 3) % 23 = 4} = 
          Finset.filter (fun x => (2 * x ^ 2 + 2 * x + 3) % 23 = 4) (Finset.Icc (2000 : ℤ) (2022 : ℤ)) := by
    ext x
    simp
    <;> omega
  rw [h1]
  rw [finsum_mem_coe_finset]
  native_decide