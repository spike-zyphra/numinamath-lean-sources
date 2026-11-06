import Mathlib

open Finset Nat 


theorem number_theory_641162 (k M : ℕ) (hk : 0 < k) (hM : 0 < M) :
  ∑ᶠ y ∈ {y : ℕ | 0 < y ∧ y ≤ M ∧ ∃ x z : ℕ, 0 < x ∧ 0 < z ∧ x ^ k * y = z ^ k}, y =
  ∑ j ∈ Finset.Icc 1 ⌊(M : ℝ) ^ (1 / k : ℝ)⌋₊, j ^ k := by 
  let f : ℕ → ℕ := fun n => n ^ k
  have kneq : k ≠ 0 := by 
    linarith
  -- prove that the following set is equal.
  have h1 : {y : ℕ | 0 < y ∧ y ≤ M ∧ ∃ x z : ℕ, 0 < x ∧ 0 < z ∧ x ^ k * y = z ^ k} = 
    image f (Icc 1 ⌊(M : ℝ) ^ (1 / k : ℝ)⌋₊) := by 
    refine Set.ext ?_
    intro y
    constructor
    · 
      intro h
      simp at h
      obtain ⟨ypos, yle, x, xpos, z, zpos, xzeq⟩ := h
      simp
      have aux1 : x ^ k ∣ z ^ k := by 
        rw [←xzeq]
        simp
      have xdvdz : x ∣ z := by 
        exact (Nat.pow_dvd_pow_iff kneq).mp aux1
      obtain ⟨m, hm⟩ := xdvdz
      use m 
      have aux : f m = y := by 
        unfold f
        rw [hm, mul_pow] at xzeq
        have neq1 : x ^ k ≠ 0 := by 
          positivity
        apply Eq.symm
        exact (Nat.mul_right_inj neq1).mp xzeq
      constructor
      · 
        constructor
        · 
          nlinarith
        · 
          refine le_floor ?_
          refine (Real.le_rpow_inv_iff_of_pos ?_ ?_ ?_).mpr ?_
          · norm_cast
            linarith
          · norm_cast
            linarith
          · norm_cast 
          · norm_cast
            unfold f at aux
            rw [aux]
            exact yle
      unfold f
      rw [hm, mul_pow] at xzeq
      have neq1 : x ^ k ≠ 0 := by 
        positivity
      apply Eq.symm
      exact (Nat.mul_right_inj neq1).mp xzeq
    · 
      intro h1
      simp at h1
      obtain ⟨m, ⟨hmge, hmle⟩, hm2⟩ := h1
      simp
      constructor
      · rw [← hm2]
        unfold f
        positivity
      constructor
      · rw [← hm2]
        unfold f
        have mle : (m : ℝ) ≤ ↑M ^ (k : ℝ)⁻¹ := by 
          refine (Nat.le_floor_iff' ?_).mp hmle 
          linarith
        have pos1 : (m : ℝ) ≥ 0 := by 
          norm_cast
          linarith
        have pos2 : (M : ℝ) ≥ 0 := by 
          norm_cast
          linarith
        have pos3 : (k : ℝ) > 0 := by 
          norm_cast
        obtain aux1 := (Real.le_rpow_inv_iff_of_pos pos1 pos2 pos3).mp mle
        norm_cast at aux1
      use 1 
      constructor
      norm_num
      use m
      constructor
      linarith
      rw [←hm2]
      unfold f
      simp
  -- use Finset.sum_image to prove the following equality.
  have h2 : ∑ j ∈ Finset.Icc 1 ⌊(M : ℝ) ^ (1 / k : ℝ)⌋₊, j ^ k = 
    ∑ j ∈ image f (Icc 1 ⌊(M : ℝ) ^ (1 / k : ℝ)⌋₊), j := by 
    rw [Finset.sum_image]
    intro i hi j hj hij
    unfold f at hij
    refine (pow_left_inj₀ ?_ ?_ ?_).mp hij
    linarith
    linarith
    linarith
  rw [h2, h1]
  exact finsum_mem_finset_eq_sum (fun i => i) (image f (Icc 1 ⌊(M : ℝ) ^ (1 / (k : ℝ))⌋₊))