import Mathlib


lemma lemma_1 (k : ℕ) (hk : k ≤ 6) :
    {x : ℕ | x < 45 ∧ x % 7 = k}.ncard ≤ 7 := by 
  have h1 : {x : ℕ | x < 45 ∧ x % 7 = k} = Finset.filter (fun x => x % 7 = k) (Finset.Iio (45 : ℕ)) := by
    ext x
    simp
  rw [h1]
  rw [Set.ncard_coe_Finset]
  interval_cases k <;> try { native_decide }

theorem number_theory_271764 :
    IsGreatest {k | ∃ m, k = {x | x ∈ Finset.range 45 ∧ (m + x) % 7 = 0}.ncard} 7 := by
  constructor 
  · -- Show that 7 is in the set
    use 0
    have h1 : {x | x ∈ Finset.range 45 ∧ (0 + x) % 7 = 0} = Finset.filter (fun x => x % 7 = 0) (Finset.range 45) := by
      ext x 
      simp 
    rw [h1]
    rw [Set.ncard_coe_Finset]
    native_decide
  · -- Show that 7 is the greatest element in the set
    intro k hk
    rcases hk with ⟨m, hm⟩
    have h2 : {x | x ∈ Finset.range 45 ∧ (m + x) % 7 = 0} = Finset.filter (fun x => (m + x) % 7 = 0) (Finset.range 45) := by
      ext x
      simp
    rw [h2] at hm
    rw [Set.ncard_coe_Finset] at hm
    have h3 : (Finset.filter (fun x => (m + x) % 7 = 0) (Finset.range 45)).card ≤ 7 := by
      have h4 : (Finset.filter (fun x => (m + x) % 7 = 0) (Finset.range 45)) = Finset.filter (fun x => x % 7 = (7 - (m % 7)) % 7) (Finset.range 45) := by
        ext x
        simp
        omega
      rw [h4]
      have h5 : (7 - (m % 7)) % 7 ≤ 6 := by 
        omega
      interval_cases h8 : (7 - (m % 7)) % 7 <;> try { native_decide }
    omega