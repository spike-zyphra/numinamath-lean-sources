import Mathlib

open Nat Finset

theorem number_theory_642036 {N : ℕ} (hN : N ≥ 4) :
  (∑ k in Finset.Icc 1 N, (k !) ^ 2) % 100 = 17 := by 
  have h1 : ∑ k ∈ Finset.Icc 1 N, k ! ^ 2 = ∑ k ∈ Finset.Icc 1 4, k ! ^ 2 + ∑ k ∈ Finset.Icc 5 N, k ! ^ 2 := by 
    have aux : Disjoint (Icc 1 4) (Icc 5 N) := by 
      refine disjoint_left.mpr ?_
      intro x hx
      simp at hx
      obtain ⟨hx1, hx2⟩ := hx
      simp
      intro h
      by_contra hc
      linarith
    have aux1 : Icc 1 N = (Icc 1 4).disjUnion (Icc 5 N) aux := by 
      refine Finset.ext_iff.mpr ?_
      intro x 
      constructor
      · intro hx
        simp at hx
        simp
        obtain ⟨hx1, hx2⟩ := hx
        by_cases hxle : x ≤ 4 
        · left
          constructor
          · exact hx1
          · exact hxle
        · right
          simp at hxle
          constructor
          · linarith
          · exact hx2
      · intro hx
        simp at hx
        simp 
        obtain ih | ih := hx
        · obtain ⟨ih1, ih2⟩ := ih
          constructor
          · linarith
          · linarith
        · obtain ⟨ih1, ih2⟩ := ih
          constructor
          · linarith
          · linarith
    rw [aux1]
    exact Finset.sum_disjUnion aux
  rw [h1, add_mod]
  have h2 : (∑ k ∈ Icc 5 N, k ! ^ 2) % 100 = 0 := by 
    rw [sum_nat_mod]
    have aux : ∑ i ∈ Icc 5 N, i ! ^ 2 % 100 = 0 := by 
      apply sum_eq_zero
      intro x hx
      simp at hx
      rcases hx with ⟨hxge, hxle⟩
      have dvd1 : 10 ∣ x ! := by 
        by_cases Nge : N ≥ 5
        · 
          have dvd2 : 2 ∣ x ! := by 
            refine dvd_factorial ?_ ?_
            · linarith
            · linarith
          have dvd3 : 5 ∣ x ! := by
            refine dvd_factorial ?_ ?_
            · linarith
            · linarith
          rw [show 10 = 2 * 5 by norm_num]
          exact Coprime.mul_dvd_of_dvd_of_dvd rfl dvd2 dvd3
        · simp at Nge
          linarith
      refine dvd_iff_mod_eq_zero.mp ?_
      rw [show 100 = 10 ^ 2 by norm_num]
      exact pow_dvd_pow_of_dvd dvd1 2
    rw [aux]
  have h3 : ∑ k ∈ Icc 1 4, k ! ^ 2 = 1 ! ^ 2 + 2 ! ^ 2 + 3! ^ 2 + 4! ^ 2 := by
    exact rfl
  have h4 : (∑ k ∈ Icc 1 4, k ! ^ 2) % 100 = 17 := by 
    rw [h3]
    rfl
  rw [h4, h2]