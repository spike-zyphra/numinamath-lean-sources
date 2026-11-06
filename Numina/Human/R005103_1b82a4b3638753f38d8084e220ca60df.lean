import Mathlib

open Finset Real

theorem algebra_605546 {n : ℕ} (hn : n ≥ 4) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 (2 * n), a i > 0)
    (ha1 : a 1 = 1 / (a (2 * n)) + 1 / a 2)
    (han_odd : ∀ i ∈ Icc 1 (n - 1), a (2 * i + 1) = 1 / a (2 * i) + 1 / a (2 * i + 2))
    (han_even : ∀ i ∈ Icc 1 (n - 1), a (2 * i) = a (2 * i - 1) + a (2 * i + 1))
    (ha2n : a (2 * n) = a (2 * n - 1) + a 1) :
    (∀ i ∈ Icc 1 n, a (2 * i) = 2) ∧ (∀ i ∈ Icc 0 (n - 1), a (2 * i + 1) = 1) := by 
  -- first prove that `∀ i ∈ Icc 1 (n), ∀ j ∈ Icc 1 (n), a (2 * i) = a (2 * j)`
  have hneq1 : ∀ i ∈ Icc 1 (n), ∀ j ∈ Icc 1 (n), a (2 * i) = a (2 * j) := by 
    let a' : ℕ → ℝ := fun x => a (2 * x)
    let s1 := image a' (Icc 1 n)
    have nonempty_s1 : s1.Nonempty := by
      unfold s1
      refine image_nonempty.mpr ?_
      simp
      linarith
    let m := min' s1 nonempty_s1
    let M := max' s1 nonempty_s1
    have hm: ∀ k ∈ Icc 1 n, a' k ≤ M := by 
      intro k hk
      unfold M
      unfold s1
      apply Finset.le_max'
      simp
      use k
      constructor
      simp at hk
      exact hk
      rfl
    have hm': ∀ k ∈ Icc 1 n, a' k ≥ m := by
      intro k hk
      unfold m
      unfold s1
      apply Finset.min'_le
      simp
      use k
      constructor
      simp at hk
      exact hk
      rfl
    have exist_i : ∃ i ∈ Icc 1 n, a' i = m := by
      unfold m
      unfold s1
      obtain h1 := Finset.min'_mem s1 nonempty_s1
      unfold s1 at h1
      simp at h1
      simp [h1]
    obtain ⟨i, hi, hieq⟩ := exist_i
    have exist_j : ∃ j ∈ Icc 1 n, a' j = M := by
      unfold M 
      unfold s1
      obtain h1 := Finset.max'_mem s1 nonempty_s1
      unfold s1 at h1
      simp at h1
      simp [h1]
    obtain ⟨j, hj, hjeq⟩ := exist_j
    -- now we use the inequality to prove m = M
    unfold a' at hieq hjeq
    have meqM : m = M := by
      have ineqaux1 : m ≥ 2 / m + 2 / M := by 
        conv =>
          rhs
          rw [←hieq]
        by_cases hi1 : i = 1
        rw [hi1, han_even 1 (by simp; omega) ] at hieq
        have aux : 2 * 1 - 1 = 1 := by norm_num
        rw [aux, ha1, han_odd 1 (by simp; omega)] at hieq
        rw [←hieq]
        obtain h1 := hm 2 (by simp; omega)
        obtain h2 := hm n (by simp; omega)
        unfold a' at h1 h2
        simp at h1 h2
        obtain h3 := ha 4 (by simp; omega)
        obtain h4 := ha (2 * n) (by simp; omega)
        have ineq1 : 1 / a 4 ≥ 1 / M := by 
          exact one_div_le_one_div_of_le h3 h1
        have ineq2 : 1 / a (2 * n) ≥ 1 / M := by
          exact one_div_le_one_div_of_le h4 h2
        rw [hi1]
        simp at ineq1 ineq2
        ring_nf
        have ineq3 : (a (n * 2))⁻¹ + (a 4)⁻¹ ≥ M⁻¹ * 2 := by
          calc 
            _ ≥ M⁻¹ + M⁻¹ := by 
              rw [mul_comm]
              linarith
            _ = _ := by
              field_simp
              norm_num
        linarith
        -- the cases i = n
        by_cases ieqn : i = n
        rw [ieqn, ha2n, ha1] at hieq
        have eq_aux : 2 * n - 1 = 2 * (n - 1) + 1 := by
          omega
        rw [eq_aux, han_odd (n - 1) (by simp; omega)] at hieq
        rw [← hieq, ieqn]
        have eq_aux1 : 2 * (n - 1) + 2 = 2 * n := by omega
        rw [eq_aux1]
        have ineq1 : 1 / a (2 * (n - 1)) + 1 / a 2 ≥ M⁻¹ * 2 := by 
          have aux1 : 1 / a (2 * (n - 1)) ≥ 1 / M := by
            obtain h1 := hm (n - 1) (by simp; omega)
            obtain h2 := ha (2 * (n - 1)) (by simp; omega)
            exact one_div_le_one_div_of_le h2 h1
          have aux2 : 1 / a 2 ≥ 1 / M := by
            obtain h1 := hm 1 (by simp; omega)
            obtain h2 := ha 2 (by simp; omega)
            exact one_div_le_one_div_of_le h2 h1
          calc 
            _ ≥ 1 / M + 1 / M := by linarith
            _ = _ := by field_simp; norm_num
        ring_nf
        simp at ineq1
        nth_rw 1 [mul_comm]
        linarith
        -- the rest case is i ∈ 2 ～ n-1
        have ilt : i < n := by 
          simp at hi
          obtain ⟨hi₁, hi₂⟩ := hi
          omega
        have ineqi : i ≤ n - 1 := by
          omega
        simp at hi
        have iin : i - 1 ∈ Icc 1 (n - 1) := by
          simp
          constructor
          omega
          omega
        have aux1 : 2 * i - 1 = 2 * (i - 1) + 1 := by omega
        have aux2 : 2 * (i - 1) + 2 = 2 * i := by omega
        have aux3 : 2 * i + 2 = 2 * (i + 1) := by omega
        rw [han_even i (by simp; omega), aux1, han_odd (i - 1) (by simp; omega), han_odd i (by simp; omega), aux2, aux3] at hieq
        have ineq1 : 1 / a (2 * (i - 1)) + 1 / a (2 * (i + 1)) ≥ 2 /M := by 
          have ineq2 : 1 / a (2 * (i - 1)) ≥ 1 / M := by
            obtain h1 := hm (i - 1) (by simp; omega)
            obtain h2 := ha (2 * (i - 1)) (by simp; omega)
            exact one_div_le_one_div_of_le h2 h1
          have ineq3 : 1 / a (2 * (i + 1)) ≥ 1 / M := by
            obtain h1 := hm (i + 1) (by simp; omega)
            obtain h2 := ha (2 * (i + 1)) (by simp; omega)
            exact one_div_le_one_div_of_le h2 h1
          calc
            _ ≥ 1 / M + 1 / M := by linarith
            _ = _ := by field_simp; norm_num
        rw [←hieq]
        calc 
          _ = (1 / a (2 * (i - 1)) + 1 / a (2 * (i + 1)) ) + (2 / a (2 * i)) := by 
            ring_nf
          _ ≥ _ := by 
            linarith
      -- the second part of inequality, use the same strategy as above we can prove the following inequality
      have ineq2 : M ≤ 2 / m + 2 / M := by 
        conv =>
          rhs
          rw [←hjeq]
        have mpos : m > 0 := by 
          rw [←hieq]
          apply ha
          simp 
          constructor
          simp at hi
          linarith
          simp at hi
          linarith
        by_cases hj1 : j = 1
        rw [hj1, han_even 1 (by simp; omega) ] at hjeq
        have aux : 2 * 1 - 1 = 1 := by norm_num
        rw [aux, ha1, han_odd 1 (by simp; omega)] at hjeq
        rw [←hjeq]
        obtain h1 := hm' 2 (by simp; omega)
        obtain h2 := hm' n (by simp; omega)
        unfold a' at h1 h2
        simp at h1 h2
        obtain h3 := ha 4 (by simp; omega)
        obtain h4 := ha (2 * n) (by simp; omega)
        have ineq1 : 1 / a 4 ≤  1 / m := by 
          exact one_div_le_one_div_of_le mpos h1
        have ineq2 : 1 / a (2 * n) ≤ 1 / m := by
          exact one_div_le_one_div_of_le mpos h2
        rw [hj1]
        calc 
          _ = 1 / a (2 * n) + 1 / a (2 * 1 + 2) + 2 / a 2 := by 
            ring

          _ ≤  _ := by 
            simp
            simp at ineq1 ineq2
            have aux3 : 2 / m = m⁻¹ + m⁻¹ := by 
              field_simp
              norm_num
            rw [aux3]
            linarith
        -- the cases i = n
        by_cases jeqn : j = n
        rw [jeqn, ha2n, ha1] at hjeq
        have eq_aux : 2 * n - 1 = 2 * (n - 1) + 1 := by
          omega
        rw [eq_aux, han_odd (n - 1) (by simp; omega)] at hjeq
        rw [← hjeq, jeqn]
        have eq_aux1 : 2 * (n - 1) + 2 = 2 * n := by omega
        rw [eq_aux1]
        have ineq1 : 1 / a (2 * (n - 1)) + 1 / a 2 ≤  m⁻¹ * 2 := by 
          have aux1 : 1 / a (2 * (n - 1)) ≤  1 / m := by
            obtain h1 := hm' (n - 1) (by simp; omega)
            exact one_div_le_one_div_of_le mpos h1
          have aux2 : 1 / a 2 ≤  1 / m := by
            obtain h1 := hm' 1 (by simp; omega)
            exact one_div_le_one_div_of_le mpos h1
          calc 
            _ ≤  1 / m + 1 / m := by linarith
            _ = _ := by field_simp; norm_num
        ring_nf
        simp at ineq1
        nth_rw 1 [mul_comm]
        linarith
        -- the rest case is i ∈ 2 ～ n-1
        have jlt : j < n := by 
          simp at hj
          obtain ⟨hi₁, hi₂⟩ := hj
          omega
        have ineqj : j ≤ n - 1 := by
          omega
        simp at hj
        have iin : j - 1 ∈ Icc 1 (n - 1) := by
          simp
          constructor
          omega
          omega
        have aux1 : 2 * j - 1 = 2 * (j - 1) + 1 := by omega
        have aux2 : 2 * (j - 1) + 2 = 2 * j := by omega
        have aux3 : 2 * j + 2 = 2 * (j + 1) := by omega
        rw [han_even j (by simp; omega), aux1, han_odd (j - 1) (by simp; omega), han_odd j (by simp; omega), aux2, aux3] at hjeq
        have ineq1 : 1 / a (2 * (j - 1)) + 1 / a (2 * (j + 1)) ≤ 2 /m := by 
          have ineq2 : 1 / a (2 * (j - 1)) ≤ 1 / m := by
            obtain h1 := hm' (j - 1) (by simp; omega)
            exact one_div_le_one_div_of_le mpos h1
          have ineq3 : 1 / a (2 * (j + 1)) ≤ 1 / m := by
            obtain h1 := hm' (j + 1) (by simp; omega)
            exact one_div_le_one_div_of_le mpos h1
          calc
            _ ≤  1 / m + 1 / m := by linarith
            _ = _ := by field_simp; norm_num
        rw [←hjeq]
        calc 
          _ = (1 / a (2 * (j - 1)) + 1 / a (2 * (j + 1)) ) + (2 / a (2 * j)) := by 
            ring_nf
          _ ≤ _ := by 
            linarith
      have mleM : m ≤ M := by 
        rw [←hieq]
        exact hm i hi
      linarith
    intro i1 hi1 j1 hj1
    rw [meqM] at hm'
    unfold a' at hm hm'
    have aux : a (2 * i1) = M := by 
      obtain h1 := hm i1 hi1
      obtain h2 := hm' i1 hi1
      exact eq_of_le_of_le h1 h2
    have aux' : a (2 * j1) = M := by
      obtain h1 := hm j1 hj1
      obtain h2 := hm' j1 hj1
      exact eq_of_le_of_le h1 h2
    rw [aux, aux']
  have eq1 : ∃ m, ∀ i ∈ Icc 1 n, a (2 * i) = m := by
    use (a 2)
    intro i hi
    have aux : 1 ∈ Icc 1 n := by 
      simp
      linarith
    obtain aux1 := hneq1 i hi 1 aux
    rw [aux1]
  obtain ⟨m, haneq1⟩ := eq1
  have hneq2 : ∀ i ∈ Icc 0 (n - 1), a (2 * i + 1) = 2 / m := by 
    intro i hi
    by_cases hi0 : i = 0
    rw [hi0, ha1]
    have nin : n ∈ Icc 1 n := by 
      simp
      linarith
    have in1 : 1 ∈ Icc 1 n := by
      simp 
      linarith
    rw [haneq1 n nin, haneq1 1 in1]
    ring
    have aux : i ∈ Icc 1 (n - 1) := by 
      simp
      simp at hi
      constructor
      omega
      exact hi
    rw [han_odd i aux, haneq1, show (2 * i + 2)= 2 * (i + 1) by ring, haneq1]
    ring
    simp
    simp at aux
    obtain ⟨aux1, aux2⟩ := aux
    omega
    simp
    simp at aux
    obtain ⟨aux1, aux2⟩ := aux
    omega
  have meq2 : m = 2 := by 
    obtain aux2 := han_even (n - 1)
    have aux3 : 2 * (n - 1) + 1 = 2 * n - 1 := by 
      omega
    have aux4 : n - 1 ∈ Icc 0 (n - 1) := by
      simp
    rw [haneq1, ←aux3, hneq2 (n - 1) aux4, show 1 = 2 * 0 + 1 by ring, hneq2 0 (by simp)] at ha2n
    have mneq : m ≠ 0 := by 
      have in_aux : 2 ∈ Icc 1 (2 * n) := by
        simp
        linarith
      have in_aux1 : 1 ∈ Icc 1 n := by 
        simp 
        linarith
      rw [←haneq1 1 in_aux1]
      obtain aux := ha 2 in_aux
      simp
      linarith
    field_simp at ha2n
    have msqeq : m ^ 2 = 2 ^ 2 := by 
      ring_nf at ha2n
      ring_nf
      exact ha2n
    have meqor : m = 2 ∨ m = -2 := by 
      refine sq_eq_sq_iff_eq_or_eq_neg.mp msqeq
    obtain meq1 | meq1 := meqor
    exact meq1
    have in_aux : 2 ∈ Icc 1 (2 * n) := by
        simp
        linarith
    have in_aux1 : 1 ∈ Icc 1 n := by 
      simp 
      linarith
    rw [←haneq1 1 in_aux1] at meq1
    obtain aux := ha 2 in_aux
    simp at meq1
    linarith
    simp
    linarith
  constructor
  · -- first goal, the even index is equal to 2
    intro i hi
    rw [haneq1 i hi]
    exact meq2
  · -- second goal, the odd index is equal to 1
    intro i hi
    rw [hneq2 i hi, meq2]
    simp