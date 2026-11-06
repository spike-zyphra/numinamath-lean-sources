import Mathlib

open Finset

noncomputable def p : ℕ → ℕ := fun n => Nat.nth (Nat.Prime) n

noncomputable def P : ℕ → ℕ := fun K => ∏ i ∈ Icc 1 K, p i 

theorem number_theory_642001 (K i j k : ℕ) (ipos : i > 0) (jpos : j > 0) (kpos : k > 0)
  (ineqj : i ≠ j) (ineqk : i ≠ k) (jneqk : j ≠ k)
  (hK : K ≥ max (max i j) k) :
  ¬ (p i) ^ 2 * p j * p k ∣ P K := by 
  -- Nat.factorization_prime_le_iff_dvd
  have h1 : ∀ n m, n ≥ 1 → m ≥ n → (P m).factorization (p n) = 1 := by 
    intro n m hn1 hmn
    refine Nat.factorization_eq_one_of_squarefree ?_ ?_ ?_
    · refine Nat.squarefree_iff_prime_squarefree.mpr ?_
      intro x hx
      unfold P
      by_contra hc 
      have xdvd : x ∣ ∏ i ∈ Icc 1 m, p i := by 
        have dvd1 : x ∣ x * x := by 
          simp
        exact Nat.dvd_trans dvd1 hc
      have prime1 : Prime x := by 
        exact Nat.prime_iff.mp hx
      obtain ⟨t, ht1, ht2⟩ := (Prime.dvd_finset_prod_iff prime1 p).mp xdvd
      have prime2 : Nat.Prime (p t) := by 
        unfold p
        exact Nat.prime_nth_prime t
      have xeqt : x = p t := by 
        exact (Nat.prime_dvd_prime_iff_eq hx prime2).mp ht2
      let s := (Icc 1 m).erase t
      have seteq : Icc 1 m = insert t s := by 
        unfold s
        exact Eq.symm (insert_erase ht1)
      rw [seteq, prod_insert, xeqt] at hc
      have dvd2 : p t ∣ ∏ x ∈ s, p x := by
        obtain ⟨m, hm⟩ := hc
        have ptneq : p t > 0 := by 
          unfold p
          exact Nat.Prime.pos prime2
        have eq_aux : ∏ x ∈ s, p x = p t * m := by 
          nlinarith
        rw [eq_aux]
        simp  
      have prime3 : Prime (p t) := by 
        exact Nat.prime_iff.mp prime2
      obtain ⟨a, ha1, ha2⟩ := (Prime.dvd_finset_prod_iff prime3 p).mp dvd2
      have prime4 : Nat.Prime (p a) := by
        unfold p
        exact Nat.prime_nth_prime a
      have eq3 : p t = p a := by 
        exact (Nat.prime_dvd_prime_iff_eq prime2 prime4).mp ha2
      have eq4 : t = a := by
        unfold p at eq3 
        obtain h3 := Nat.nth_injective Nat.infinite_setOf_prime
        unfold Function.Injective at h3
        exact h3 eq3
      unfold s at ha1
      rw [←eq4] at ha1
      simp at ha1
      unfold s
      simp
    · unfold p
      exact Nat.prime_nth_prime n
    · unfold p P
      apply dvd_prod_of_mem
      simp
      constructor
      · exact hn1
      · exact hmn
  by_contra hc
  have neq1 : p i ^ 2 * p j * p k ≠ 0 := by 
    have pos : p i ^ 2 * p j * p k > 0 := by 
      unfold p 
      have pos1 : Nat.nth Nat.Prime i > 0 := by 
        have prime1 : Nat.Prime (Nat.nth Nat.Prime i) := by 
          exact Nat.prime_nth_prime i
        exact Nat.Prime.pos prime1
      have pos2 : Nat.nth Nat.Prime j > 0 := by 
        have prime2 : Nat.Prime (Nat.nth Nat.Prime j) := by 
          exact Nat.prime_nth_prime j
        exact Nat.Prime.pos prime2
      have pos3 : Nat.nth Nat.Prime k > 0 := by 
        have prime3 : Nat.Prime (Nat.nth Nat.Prime k) := by 
          exact Nat.prime_nth_prime k
        exact Nat.Prime.pos prime3
      positivity
    linarith
  have neq2 : P K ≠ 0 := by 
    unfold P
    refine Finset.prod_ne_zero_iff.mpr ?_ 
    intro a ha 
    unfold p
    have pos1 : Nat.nth Nat.Prime a > 0 := by 
      have prime1 : Nat.Prime (Nat.nth Nat.Prime a) := by 
        exact Nat.prime_nth_prime a
      exact Nat.Prime.pos prime1
    linarith
  have prime1 : Nat.Prime (p i) := by 
    unfold p
    exact Nat.prime_nth_prime i
  obtain h2 := (Nat.factorization_prime_le_iff_dvd neq1 neq2).mpr hc (p i) prime1
  have eq1 : (p i ^ 2 * p j * p k).factorization (p i)  = 2 := by 
    rw [←Nat.multiplicity_eq_factorization]
    refine multiplicity_eq_of_dvd_of_not_dvd ?_ ?_
    · rw [mul_assoc]
      simp
    · rw [pow_add]
      by_contra hc 
      obtain ⟨m, hm⟩ := hc
      have pos : p i > 0 := by 
        exact Nat.Prime.pos prime1
      have eq1 : p j * p k =  p i ^ 1 * m := by 
        nlinarith
      simp at eq1
      obtain h3 := Nat.nth_injective Nat.infinite_setOf_prime
      have primei : Nat.Prime (p i) := by 
        unfold p
        exact prime1
      have primej : Nat.Prime (p j) := by 
        unfold p
        exact Nat.prime_nth_prime j
      have primek : Nat.Prime (p k) := by 
        unfold p
        exact Nat.prime_nth_prime k
      have pdvd : p i ∣ p j * p k := by 
        rw [eq1]
        simp
      have dvd_or: p i ∣ p j ∨ p i ∣ p k := by 
        exact (Nat.Prime.dvd_mul primei).mp pdvd
      unfold Function.Injective at h3
      obtain dvd1 | dvd2 := dvd_or 
      · have pieqpj : p i = p j := by
          exact (Nat.prime_dvd_prime_iff_eq primei primej).mp dvd1
        obtain ieqj := h3 pieqpj
        exact ineqj ieqj
      · have pieqpk : p i = p k := by
          exact (Nat.prime_dvd_prime_iff_eq primei primek).mp dvd2
        obtain ieqk := h3 pieqpk
        exact ineqk ieqk
    exact prime1
    exact neq1
  have eq2 : (P K).factorization (p i) = 1 := by 
    apply h1
    · linarith
    · have kge1 : K ≥ max i j := by 
        exact le_of_max_le_left hK
      exact le_of_max_le_left kge1
  rw [eq1, eq2] at h2
  linarith