import Mathlib

theorem algebra_274640 :
  {P : Polynomial ℤ | ∃ n : ℕ, P.degree = n ∧
    n + ∑ i ∈ Finset.range (n + 1), |P.coeff i| = 3 ∧
    P.coeff n > 0
  }.encard = 5 := by

  let S := {P : Polynomial ℤ | ∃ n : ℕ, P.degree = n ∧
    n + ∑ i ∈ Finset.range (n + 1), |P.coeff i| = 3 ∧
    P.coeff n > 0
  }

  let P1 := Polynomial.C (3 : ℤ)
  let P2 := Polynomial.X + Polynomial.C (1 : ℤ)
  let P3 := Polynomial.X + Polynomial.C (-1 : ℤ)
  let P4 := Polynomial.C (2 : ℤ) * Polynomial.X
  let P5 : Polynomial ℤ := Polynomial.X ^ 2

  have hP1 : P1 ∉ ({P2, P3, P4, P5}: Set (Polynomial ℤ)) := by
    have h12 : P1 ≠ P2 := by
      have h0 : P1.coeff 0 = 3 := by simp [P1]
      have h0' : P2.coeff 0 = 1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h13 : P1 ≠ P3 := by
      have h0 : P1.coeff 0 = 3 := by simp [P1]
      have h0' : P3.coeff 0 = -1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h14 : P1 ≠ P4 := by
      have h0 : P1.coeff 0 = 3 := by simp [P1]
      have h0' : P4.coeff 0 = 0 := by simp [P4]
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h15 : P1 ≠ P5 := by
      have h0 : P1.coeff 0 = 3 := by simp [P1]
      have h0' : P5.coeff 0 = 0 := by simp [P5]
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    simp
    tauto

  have hP2 : P2 ∉ ({P3, P4, P5}: Set (Polynomial ℤ)) := by
    have h23 : P2 ≠ P3 := by
      have h0 : P2.coeff 0 = 1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      have h0' : P3.coeff 0 = -1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h24 : P2 ≠ P4 := by
      have h0 : P2.coeff 0 = 1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      have h0' : P4.coeff 0 = 0 := by simp [P4]
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h25 : P2 ≠ P5 := by
      have h1 : P2.coeff 1 = 1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      have h1' : P5.coeff 1 = 0 := by rw [Polynomial.coeff_X_pow]; simp
      intro h_eq
      rw [h_eq] at h1
      rw [h1'] at h1
      norm_num at h1

    simp
    tauto

  have hP3 : P3 ∉ ({P4, P5}: Set (Polynomial ℤ)) := by
    have h34 : P3 ≠ P4 := by
      have h0 : P3.coeff 0 = -1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      have h0' : P4.coeff 0 = 0 := by simp [P4]
      intro h_eq
      rw [h_eq] at h0
      rw [h0'] at h0
      norm_num at h0

    have h35 : P3 ≠ P5 := by
      have h1 : P3.coeff 1 = 1 := by rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      have h1' : P5.coeff 1 = 0 := by rw [Polynomial.coeff_X_pow]; simp
      intro h_eq
      rw [h_eq] at h1
      rw [h1'] at h1
      norm_num at h1

    simp
    tauto

  have hP4 : P4 ∉ ({P5}: Set (Polynomial ℤ)) := by
    simp
    by_contra h
    have h1 : P4.coeff 1 = 2 := by rw [Polynomial.coeff_mul_X, Polynomial.coeff_C]; simp
    have h1' : P5.coeff 1 = 0 := by rw [Polynomial.coeff_X_pow]; simp
    rw [h, h1'] at h1
    norm_num at h1

  suffices S = {P1, P2, P3, P4, P5} by
    unfold S at this
    rw [this]
    rw [Set.encard_insert_of_not_mem hP1]
    rw [Set.encard_insert_of_not_mem hP2]
    rw [Set.encard_insert_of_not_mem hP3]
    rw [Set.encard_insert_of_not_mem hP4]
    simp; norm_num

  unfold S
  ext P
  simp
  constructor
  . intro ⟨n, hn, h1, h2⟩
    have h_max : n ≤ 2 := by
      by_contra hn
      have : n ≥ 3 := by omega
      have : ∑ i ∈ Finset.range (n + 1), |P.coeff i| ≤ 0 := by linarith
      rw [Finset.sum_range_succ] at this
      rw [abs_of_pos h2] at this
      have : ∑ x ∈ Finset.range n, |P.coeff x| < 0 := by linarith
      have : ∑ x ∈ Finset.range n, |P.coeff x| ≥ 0 := by positivity
      omega

    interval_cases n
    all_goals simp at h1
    . left
      unfold P1
      rw [abs_of_pos h2] at h1
      rw [← h1]
      apply Polynomial.eq_C_of_degree_eq_zero
      exact hn
    . right
      rw [Finset.sum_range_succ] at h1
      simp at h1
      nth_rw 2 [abs_of_pos (by linarith)] at h1
      have : |P.coeff 0| ≥ 0 := by positivity
      have : P.coeff 1 ≤ 2 := by linarith
      by_cases h3 : P.coeff 1 = 1
      . have : |P.coeff 0| = 1 := by linarith
        rw [abs_eq (by norm_num)] at this
        rcases this with h0 | h0
        . left
          have ha: P.degree ≤ 1 := by rw [hn]; norm_cast
          have hb: P2.degree ≤ 1 := by rw [Polynomial.degree_add_C (by norm_num), Polynomial.degree_X]
          rw [Polynomial.ext_iff_degree_le ha hb]
          unfold P2
          intro n hn
          interval_cases n
          . rw [h0]; simp
          . rw [h3]; rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
        . right; left
          have ha: P.degree ≤ 1 := by rw [hn]; norm_cast
          have hb: P3.degree ≤ 1 := by rw [Polynomial.degree_add_C (by norm_num), Polynomial.degree_X]
          rw [Polynomial.ext_iff_degree_le ha hb]
          unfold P3
          intro n hn
          interval_cases n
          . rw [h0]; simp
          . rw [h3]; rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      . right; right; left
        have h3 : P.coeff 1 = 2 := by omega
        have : |P.coeff 0| = 0 := by linarith
        simp at this
        have ha: P.degree ≤ 1 := by rw [hn]; norm_cast
        have hb: P4.degree ≤ 1 := by rw [Polynomial.degree_mul, Polynomial.degree_C (by norm_num), Polynomial.degree_X]; simp
        rw [Polynomial.ext_iff_degree_le ha hb]
        intro n hn
        unfold P4
        interval_cases n
        . rw [this]; simp
        . rw [h3]; simp
    . right; right; right; right
      repeat rw [Finset.sum_range_succ] at h1
      simp at h1
      rw [abs_of_pos h2] at h1
      have : |P.coeff 0| ≥ 0 := by positivity
      have : |P.coeff 1| ≥ 0 := by positivity
      have hp0: |P.coeff 0| = 0 := by linarith
      have hp1: |P.coeff 1| = 0 := by linarith
      rw [hp0, hp1] at h1
      have hp2: P.coeff 2 = 1 := by linarith
      simp at hp0 hp1
      unfold P5
      have ha: P.degree ≤ 2 := by rw [hn]; norm_cast

      have hb: (Polynomial.X ^ 2: Polynomial ℤ).degree ≤ 2 := by rw [Polynomial.degree_X_pow]; simp

      rw [Polynomial.ext_iff_degree_le ha hb]
      intro n hn
      interval_cases n
      . rw [hp0]; simp
      . rw [hp1]; simp
      . rw [hp2]; simp


  . intro h
    rcases h with rfl | rfl | rfl | rfl | rfl
    . unfold P1
      refine ⟨0, ?_, ?_, ?_⟩
      . rw [Polynomial.degree_C (by norm_num)]; simp
      . simp
      . simp [Polynomial.coeff_C]
    . unfold P2
      refine ⟨1, ?_, ?_, ?_⟩
      . rw [Polynomial.degree_add_C (by norm_num), Polynomial.degree_X]; simp
      . rw [Finset.sum_range_succ, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      . rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
    . unfold P3
      refine ⟨1, ?_, ?_, ?_⟩
      . rw [Polynomial.degree_add_C (by norm_num), Polynomial.degree_X]; simp
      . rw [Finset.sum_range_succ, Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
      . rw [Polynomial.coeff_add, Polynomial.coeff_X, Polynomial.coeff_C]; simp
    . unfold P4
      refine ⟨1, ?_, ?_, ?_⟩
      . rw [Polynomial.degree_mul, Polynomial.degree_C (by norm_num), Polynomial.degree_X]; simp
      . rw [Finset.sum_range_succ]; simp
      . rw [Polynomial.coeff_mul_X, Polynomial.coeff_C]; simp
    . unfold P5
      refine ⟨2, ?_, ?_, ?_⟩
      . rw [Polynomial.degree_X_pow]
      . rw [Finset.sum_range_succ, Finset.sum_range_succ, Polynomial.coeff_X_pow]; simp
      . rw [Polynomial.coeff_X_pow]; simp
