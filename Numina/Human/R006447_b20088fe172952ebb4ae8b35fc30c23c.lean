import Mathlib

open Nat Finset

lemma finset_prod_neg {ι α: Type*}  {s: Finset ι}  {f : ι → α} [CommMonoid α] [HasDistribNeg α] : ∏ x ∈ s, -f x = (-1) ^ #s * ∏ x ∈ s, f x := by
  simpa using (s.1.map f).prod_map_neg

theorem number_theory_637156 {p : ℕ} (hp : p.Prime) (h : p ≡ 3 [MOD 4]) :
  p ∣ (p - 2).doubleFactorial + (p - 1).doubleFactorial := by 
  zify
  have eq1 : ↑(p - 2)‼ + ((p - 1)‼ : ℤ) = ↑(p - 2)‼ - ( - ↑(p - 1)‼) := by 
    ring
  rw [eq1]
  apply Int.ModEq.dvd
  have h1 : ∃ k, p = 4 * k + 3 := by 
    have dvd1 : (4 : ℤ) ∣ p - 3 := by
      obtain h' := Nat.ModEq.symm h
      exact Nat.ModEq.dvd h'
    obtain ⟨k, hk⟩ := dvd1
    use k.toNat
    have kge : k ≥ 0 := by 
      by_contra hc
      simp at hc
      have kle : k ≤ -1 := by omega
      linarith
    omega
  obtain ⟨k, hk⟩ := h1
  by_cases hk0 : k = 0 
  rw [hk0] at hk
  rw [hk]
  rfl
  -- the case k ≥ 1 
  have psub1 : p - 1 = 2 * (2 * k + 1) := by 
    rw [hk]
    omega
  have psub2 : p - 2 = 2 * (2 * k) + 1:= by omega
  rw [psub2, doubleFactorial_eq_prod_odd]
  have mod1 : ↑(p - 1)‼ ≡ - (∏ i ∈ Finset.range (2 * k), -(2 * (i + 1) + 1 : ℤ)) [ZMOD p] := by 
    have aux : range (2 * k + 1) = insert (2 * k) (range (2 * k)) := by 
      exact range_add_one
    rw [psub1, doubleFactorial_eq_prod_even, aux, prod_insert]
    unfold Int.ModEq
    simp
    rw [Int.mul_emod]
    have aux2 : 2 * (2 * ↑k + 1) % (p : ℤ) = -1 % p := by 
      apply Int.modEq_of_dvd
      rw [hk]
      norm_num
      use (-1)
      ring
    rw [aux2, ←Int.mul_emod]
    simp
    have aux3 : (∏ x ∈ range (2 * k), 2 * (↑x + 1 : ℤ)) % p = (∏ x ∈ range (2 * k), (-1 + -(2 * (↑x + 1 : ℤ)))) % ↑p := by 
      rw [prod_int_mod]
      conv => 
        rhs
        rw [prod_int_mod]
      -- use Finset.prod_nbij' to prove the two prod are equal
      have aux4 : (∏ i ∈ range (2 * k), 2 * (↑i + 1) % (p : ℤ))  = (∏ i ∈ range (2 * k), (-1 + -(2 * ((i : ℤ) + 1))) % ↑p) := by 
        let t : ℕ → ℕ := fun i => 2 * k - 1 - i
        refine prod_nbij' t t ?_ ?_ ?_ ?_ ?_ 
        · simp
          intro i hi
          unfold t
          omega
        · simp
          intro i hi
          unfold t
          omega
        · simp 
          intro i hi
          unfold t
          omega
        · simp 
          intro i hi
          unfold t 
          omega
        · intro a ha
          unfold t
          apply Eq.symm
          apply Int.modEq_of_dvd
          ring_nf 
          have cast1 : ↑(k * 2 - 1 - a : ℕ) = (k : ℤ) * 2 - 1 - a := by
            calc 
              _ = (k * 2 - 1 : ℕ) - (a : ℤ) := by 
                have ge_aux : k * 2 - 1 ≥ a := by 
                  simp at ha
                  omega
                omega
              _ = _ := by 
                have ge_aux : k * 2 ≥ 1 := by 
                  have kge1 : k ≥ 1 := by omega
                  linarith
                omega
          rw [cast1]
          ring_nf 
          rw [hk]
          norm_cast 
          use 1
          ring_nf
      rw [aux4]
    obtain aux4 := Int.ModEq.dvd (Int.ModEq.symm aux3)
    apply Int.modEq_of_dvd 
    simp
    rw [add_comm]
    obtain ⟨t, ht⟩ := aux4
    use t 
    rw [←ht]
    ring_nf 
    congr
    funext x
    norm_cast
    ring 
    simp
  calc 
    _ ≡ - -∏ i ∈ range (2 * k), -(2 * (↑i + 1) + 1) [ZMOD p] := by 
      exact Int.neg_modEq_neg.mpr mod1
    _ ≡ _ [ZMOD p] := by 
      rw [finset_prod_neg]
      simp