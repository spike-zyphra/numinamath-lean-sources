import Mathlib

theorem number_theory_313702 :
    ∑ᶠ a ∈ {x : ℕ | 0 < x ∧ 192 ∣ (x^3 + 191) ∧ x < 2009}, a = 10571 := by

  have h1 : {x : ℕ | 0 < x ∧ 192 ∣ (x^3 + 191) ∧ x < 2009} = Finset.filter (fun x => 0 < x ∧ 192 ∣ (x^3 + 191) ∧ x < 2009) (Finset.Icc (0 : ℕ) 2008) := by
    ext n
    simp
    omega
  rw [h1] at *
  rw [finsum_mem_coe_finset]
  native_decide