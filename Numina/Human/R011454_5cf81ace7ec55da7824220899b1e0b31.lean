import Mathlib

open Real

namespace algebra_247560
noncomputable def angle : ℝ → ℝ := fun x => π * x / 180

end algebra_247560

open algebra_247560

theorem algebra_247560 : ∏ i ∈ Finset.range 59, (1 - cos (angle (61 + i)) / cos ((angle (1 + i)))) = 1:= by 
  
  have h2 : (∏ i ∈ Finset.range 59, cos (angle (60 - (1 + i)))) = (∏ i ∈ Finset.range 59, cos (angle (1 + i))) := by 
    let bij : ℕ → ℕ := fun i => 58 - i
    let bij' : ℕ → ℕ := fun i => 58 - i
    refine Finset.prod_nbij' bij bij' ?_ ?_ ?_ ?_ ?_ 
    intro i hi
    simp at hi
    simp 
    unfold bij
    omega
    intro i hi
    simp
    unfold bij'
    omega
    intro i hi
    unfold bij
    unfold bij'
    simp at hi
    omega
    intro i hi
    simp at hi
    unfold bij
    unfold bij'
    omega
    intro i hi
    unfold bij
    have eq1 : (60 - (1 + (i : ℤ))) = (1 + ↑(58 - i)) := by 
      simp at hi
      omega
    have eq2 : (60 - (1 + (i : ℝ))) = (1 + ↑(58 - i)) := by 
      norm_cast
      norm_cast at eq1
    rw [eq2]
  have haux : ∀ (i : ℕ), i ∈ Finset.range 59 → cos (angle (1 + i)) ≠ 0 := by
    intro i hi
    unfold angle 
    by_contra hc
    obtain ⟨k, aux1⟩ := Real.cos_eq_zero_iff.mp hc
    simp at hi
    have ineq1 : π * (1 + ↑i) / 180  < π / 2 := by 
      refine (div_lt_iff₀ ?_).mpr ?_
      linarith
      have lt_aux : (i : ℝ) < 59 := by 
        norm_cast
      have aux2 : π / 2 * 180 = π * 90 := by 
        field_simp
        ring
      rw [aux2]
      refine (mul_lt_mul_left ?_).mpr ?_
      positivity
      linarith
    rw [aux1] at ineq1
    have ineq2 : (2 * (k : ℝ) + 1) < 1 := by
      by_contra hc
      have aux3 : (2 * (k : ℝ) + 1) ≥ 1 := by 
        simp
        simp at hc
        exact hc
      have pos : π > 0 := by positivity
      nlinarith
    have ineq3 : (2 * ↑k + 1) * π / 2 > - π / 2 := by 
      rw [←aux1]
      have pos : π > 0 := by positivity
      have ineq_aux : (1 + (i : ℝ)) / 180 > - 1 / 2 := by 
        refine (div_lt_div_iff₀ ?_ ?_).mpr ?_
        linarith
        linarith
        linarith
      nlinarith
    have ineq4 : (2 * (k : ℝ) + 1) > -1 := by
      by_contra hc
      have aux3 : (2 * (k : ℝ) + 1) ≤ -1 := by 
        simp at hc
        exact hc
      have pos : π > 0 := by positivity
      nlinarith
    norm_cast at ineq2
    norm_num at ineq4
    have odd : Odd (2 * k + 1) := by 
      unfold Odd
      use k
    have ineq5 : 2 * k + 1 > -1 := by 
      norm_cast at ineq4
    interval_cases (2 * k + 1)
    obtain hc := Int.not_even_iff_odd.mpr odd
    exact hc (Even.zero)
  have h3 : ∏ i ∈ Finset.range 59, cos (angle (1 + i)) ≠ 0 := by 
    refine Finset.prod_ne_zero_iff.mpr (haux)
  have h1 : ∀ (i : ℕ), i ∈ Finset.range 59 → 1 - cos (angle (61 + ↑i)) / cos (angle (1 + ↑i))
    = cos (angle (60 - (1 + i))) / cos (angle (1 + i)) := by 
    intro i hi
    obtain aux := haux i hi
    field_simp
    rw [Real.cos_sub_cos]
    have eq1 : (angle (1 + ↑i) - angle (61 + ↑i)) / 2= - π / 6 := by 
      unfold angle 
      field_simp
      ring_nf
    rw [eq1]
    have eq2 : sin (-π / 6) = - 1 / 2 := by 
      have auxneg : - π / 6 = - (π / 6) := by 
        field_simp
      simp [auxneg, Real.sin_neg]
      field_simp
    rw [eq2]
    field_simp
    have eq3 : π / 2 - ((angle (1 + ↑i) + angle (61 + ↑i)) / 2) = 
      angle (60 - (1 + ↑i)) := by 
      unfold angle
      field_simp
      ring
    rw [←eq3]
    exact Eq.symm (cos_pi_div_two_sub ((angle (1 + ↑i) + angle (61 + ↑i)) / 2))
  calc 
    _ = ∏ i ∈ Finset.range 59, cos (angle (60 - (1 + i))) / cos (angle (1 + i)) := by 
      apply Finset.prod_congr
      simp
      intro x hx
      exact (h1 x hx)
    _ = (∏ i ∈ Finset.range 59, cos (angle (60 - (1 + i)))) / (∏ i ∈ Finset.range 59, cos (angle (1 + i))) := by 
      exact Finset.prod_div_distrib
    _ = 1 := by 
      rw [h2]
      field_simp
