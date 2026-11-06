import Mathlib

open Real

theorem number_theory_642106 {N : ℕ} (hN : N ≠ 0) :
  ∏ d ∈ N.divisors, d = (N : ℝ) ^ ((Nat.divisors N).card / (2 : ℝ)) := by 
  -- first prove that (∏ d ∈ N.divisors, d : ℝ) * (∏ d ∈ N.divisors, d : ℝ) = (N : ℝ) ^ ((Nat.divisors N).card : ℝ)
  have h1 : (∏ d ∈ N.divisors, d : ℝ) * (∏ d ∈ N.divisors, d : ℝ) = 
    (N : ℝ) ^ ((Nat.divisors N).card : ℝ) := by
    have aux1 : ∏ d ∈ N.divisors, ↑d  = ∏ d ∈ N.divisors, (N / d : ℝ) := by 
      let t : ℕ → ℕ := fun x => N / x 
      refine Finset.prod_nbij' t t ?_ ?_ ?_ ?_ ?_ 
      · simp
        intro x hx1 hx2
        unfold t 
        constructor
        obtain ⟨k, hk⟩ := hx1
        rw [hk, mul_comm]
        have aux1 : k * x / x = k := by 
          refine Nat.mul_div_left k ?_
          by_contra hc
          simp at hc
          simp [hc] at hk
          exact hx2 hk
        rw [aux1]
        simp
        exact hx2
      · simp
        intro x hx1 hx2
        unfold t 
        constructor
        obtain ⟨k, hk⟩ := hx1
        rw [hk, mul_comm]
        have aux1 : k * x / x = k := by 
          refine Nat.mul_div_left k ?_
          by_contra hc
          simp at hc
          simp [hc] at hk
          exact hx2 hk
        rw [aux1]
        simp
        exact hx2
      · simp
        intro d dvd1 neq 
        unfold t 
        obtain ⟨k, hk⟩ := dvd1
        rw [hk]
        have aux1 : d * k / d = k := by 
          refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl)
          by_contra hc
          simp [hc] at hk
          exact neq hk
        rw [aux1] 
        refine Nat.mul_div_left d ?_
        by_contra hc
        simp at hc
        simp [hc] at hk
        exact neq hk 
      · simp
        intro d dvd1 neq 
        unfold t 
        obtain ⟨k, hk⟩ := dvd1
        rw [hk]
        have aux1 : d * k / d = k := by 
          refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl)
          by_contra hc
          simp [hc] at hk
          exact neq hk
        rw [aux1] 
        refine Nat.mul_div_left d ?_
        by_contra hc
        simp at hc
        simp [hc] at hk
        exact neq hk 
      · simp
        intro d dvd1 neq
        unfold t
        obtain ⟨k, hk⟩ := dvd1
        rw [hk]
        have aux1 : d * k / d = k := by 
          refine Eq.symm (Nat.eq_div_of_mul_eq_right ?_ rfl)
          by_contra hc
          simp [hc] at hk
          exact neq hk
        rw [aux1]
        simp
        have kneq : (k : ℝ) ≠ 0 := by 
          norm_cast
          by_contra hc
          simp [hc] at hk
          exact neq hk
        field_simp
    nth_rw 1 [aux1]
    rw [←Finset.prod_mul_distrib]
    calc 
      _ = ∏ x ∈ N.divisors, ↑N := by 
        apply Finset.prod_congr rfl
        simp
        intro d dvd neq
        obtain ⟨k, hk⟩ := dvd
        have dneq : (d : ℝ) ≠ 0 := by 
          norm_cast
          by_contra hc
          simp [hc] at hk
          exact neq hk
        field_simp
      _ = _ := by 
        simp
  have h2 : (∏ d ∈ N.divisors, d : ℝ) ^ (2 : ℝ) = (N : ℝ) ^ ((Nat.divisors N).card : ℝ) := by 
    rw [←h1]
    ring_nf
    simp
  have h3 : ((∏ d ∈ N.divisors, d : ℝ) ^ (2 : ℝ)) ^ (1 / (2 : ℝ))  
    = (N ^ ((Nat.divisors N).card : ℝ)) ^ (1 / (2 : ℝ)) := by 
    rw [h2]
  rw [←rpow_mul, ←rpow_mul] at h3
  simp at h3
  norm_num
  rw [h3]
  congr
  linarith
  apply Finset.prod_nonneg
  intro i hi
  norm_cast
  linarith