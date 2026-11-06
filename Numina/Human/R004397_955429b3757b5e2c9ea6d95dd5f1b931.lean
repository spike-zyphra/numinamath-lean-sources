import Mathlib

open Real Finset

theorem algebra_260562 (x : ℕ → ℝ) (hx1 : x 1 = 1 / 2)
    (hxn : ∀ k ≥ 1, x (k + 1) = x k + (x k)^2) :
    ⌊∑ i ∈ Finset.Icc 1 100, 1 / (x i + 1)⌋ = 1 := by 
  have neq1 : ∀ k ≥ 1, x k > 0 := by 
      intro k hk
      induction' k with k ih
      linarith
      by_cases hk0 : k = 0 
      simp [hk0, hx1]
      have kge1 : k ≥ 1 := by exact Nat.one_le_iff_ne_zero.mpr hk0
      obtain h1 := ih kge1
      obtain h2 := hxn k kge1
      rw [h2]
      positivity
  have neq2 : ∀ k ≥ 1, x k ≠ 0 := by
    intro k hk
    obtain h1 := neq1 k hk
    linarith
  have neq3 : ∀ k ≥ 1, x k + 1 ≠ 0 := by 
    intro k hk
    obtain h1 := neq1 k hk
    linarith
  have eq1 : ∀ k ≥ 1, 1 / (x k + 1) = 1 / (x k) - 1 / (x (k + 1)) := by 
    
    intro k hk
    obtain h1 := neq2 k hk
    obtain h2 := neq2 (k + 1) (by linarith)
    obtain h3 := neq3 k hk
    field_simp
    rw [hxn k hk]
    ring
  -- Sum over finite series using telescoping nature of terms.
  have eq2 : ∑ i ∈ Finset.Icc 1 100, 1 / (x i + 1) = ∑ i ∈ Finset.Icc 1 100, (1 / (x i) - 1 / (x (i+1))) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hige : i ≥ 1 := by 
      simp at hi
      exact hi.1
    exact eq1 i hige
  have eq3 : ∑ i ∈ Finset.Icc 1 100, (1 / x i - 1 / x (i + 1)) = 1 / x 1 - 1 / x 101 := by
    rw [Finset.sum_sub_distrib]
    have aux : ∑ x_1 ∈ Icc 1 100, 1 / x (x_1 + 1) = 
      ∑ i ∈ Icc 2 101, 1 / x i := by
      exact rfl
    rw [aux]
    have aux1 : ∑ i ∈ Icc 2 101, 1 / x i = ∑ i ∈ Icc 2 100, 
      1 / x i + 1 / x 101 := by
      have h1 : Icc 2 101 = insert 101 (Icc 2 100):= by
        ext x
        constructor
        intro h2
        simp
        simp at h2
        omega
        intro h2
        simp at h2
        simp
        omega
      rw [h1]
      rw [Finset.sum_insert]
      ring
      simp
    have aux2 : ∑ i ∈ Icc 1 100, 1 / x i = 1 / x 1 + ∑ i ∈ Icc 2 100, 1 / x i := by
      have h1 : Icc 1 100 = insert 1 (Icc 2 100):= by
        ext x
        constructor
        intro h2
        simp
        simp at h2
        omega
        intro h2
        simp at h2
        simp
        omega
      rw [h1, Finset.sum_insert]
      ring_nf
      simp
    rw [aux1, aux2]
    ring
  rw [eq2, eq3]
  have eq4 : 1 / x 1 = 2 := by
    rw [hx1]
    ring
  -- prove that x 101 > 1, then we can deduce that 1 / x 1 - 1 / x 101 > 1 and 1 / x 1 - 1 / x 101 < 2
  have ineq1 : x 101 > 0 := by
    apply neq1
    linarith
  have ineq2 : 1 / x 1 - 1 / x 101 < 2 := by 
    rw [eq4]
    have pos : 1 / x 101 > 0 := by positivity
    linarith
  have ge_aux : x 101 > 1 := by 
    have monox : ∀ k ≥ 1 , x (k + 1) > x k := by
      intro k hk
      rw [hxn]
      have pos : x k ^ 2 > 0 := by 
        obtain higt := neq1 k hk
        positivity
      linarith
      exact hk
    have ineq_aux : x 3 > 1 := by 
      rw [hxn 2 (by linarith)]
      rw [hxn 1 (by linarith)]
      rw [hx1]
      linarith
    have xge3 : ∀ k ≥ 3, x k ≥ x 3 := by 
      intro k hk
      induction' k with k ih
      linarith
      by_cases hk0 : k < 2
      linarith
      simp at hk0
      by_cases hk2 : k = 2 
      rw [hk2]
      have hk3 : k ≥ 3 := by omega
      obtain ih1 := ih hk3
      calc 
        _ ≥ x (k) := by 
          obtain h2 := monox k (by linarith)
          linarith
        _ ≥ x 3 := by 
          exact ih1
    have aux : ∀ k ≥ 3, x k > 1 := by 
      intro k hk
      obtain h1 := xge3 k hk
      linarith
    apply aux
    linarith
  have ineq3 : 1 / x 1 - 1 / x 101 > 1 := by
    rw [hx1]
    have ineq_aux : 1 / x 101 < 1 := by 
      exact Bound.div_lt_one_of_pos_of_lt ineq1 ge_aux
    linarith
  refine Int.floor_eq_iff.mpr ?_
  constructor
  linarith
  linarith