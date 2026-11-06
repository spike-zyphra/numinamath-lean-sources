import Mathlib

/- Problem 7.8. Carlson and Little Man have several jars of jam, each weighing an integer number of pounds.

The total weight of all the jars of jam that Carlson has is 13 times the total weight of all the jars that Little Man has. Carlson gave Little Man the jar with the smallest weight (from those he had), after which the total weight of his jars turned out to be 8 times the total weight of Little Man's jars.

What is the maximum number of jars of jam that Carlson could have had initially? -/

theorem number_theory_100752 :
    IsGreatest {n : ℕ | ∃ npos : n > 0,  ∃ m : ℕ, ∃ a : Fin n → ℕ, ∃ b : Fin m → ℕ,
      Monotone a ∧ (∀ i, a i > 0) ∧ Monotone b ∧ (∀ i, b i > 0) ∧
        (∑ i, a i = 13 * ∑ i, b i) ∧
          (∑ i, a i - a ⟨0, by assumption⟩ =
            8 * (a ⟨0, by assumption⟩ + ∑ i, b i))} 23 := by

  constructor
  -- We show a solution for n = 23
  · use (by linarith)
    use 1
    use fun i => match i with
      | ⟨22, _⟩ => 7
      | ⟨_, _⟩ => 5
    use fun _ => 9
    simp only [PNat.val_ofNat, gt_iff_lt, Nat.ofNat_pos, implies_true, Finset.univ_unique,
      Fin.default_eq_zero, Fin.isValue, Finset.sum_const, Finset.card_singleton, smul_eq_mul,
      one_mul, Nat.reduceMul, Nat.reduceAdd, true_and]
    all_goals decide
  -- We show that the solution is maximal
  · intro n hn
    obtain ⟨npos, m, a, b, ha, ha0, hb, hb0, h1, h2⟩ := hn

    -- Combining the hypotheses, we get a linear equation involving a 0 and ∑ i, b i
    have h : 5 * ∑ i, b i = 9 * a ⟨0, npos⟩ := by omega

    -- It follows that 5 divides a 0, so a 0 = 5 * k for some k
    obtain ⟨k, hk⟩ : 5 ∣ a ⟨0, npos⟩ := by
      have : 5 ∣ 9 * a ⟨0, npos⟩ := by
        rw [← h]
        exact Nat.dvd_mul_right 5 (∑ i : Fin m, b i)
      exact Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) this

    -- We need to establish that k is positive
    have hk0 : 0 < k := by
      apply pos_of_mul_pos_right ?_ (by norm_num : 0 ≤ 5)
      rw [← hk]
      exact ha0 ⟨0, npos⟩

    -- By substituting back, we get that ∑ i, a i = 117 * k
    have h117 : ∑ i, a i = 117 * k := by
      have : ∑ i, b i = 9 * k := by
        rw [hk, ← mul_assoc, mul_comm 9 5, mul_assoc] at h
        exact Nat.mul_left_cancel (by norm_num : 0 < 5) h
      rw [h1, this]
      ring

    -- Since a 0 is the smallest jar, the total weight is at most n times the weight of the smallest jar
    have hsum : n * a ⟨0, npos⟩ <= ∑ i, a i := by
      have : n * a ⟨0, npos⟩ = ∑ i : Fin n, a ⟨0, npos⟩ := by simp
      rw [this]
      apply Finset.sum_le_sum
      intro i hi
      apply ha
      simp [Fin.le_iff_val_le_val]

    -- So we get that n * a 0 <= 117 * k. But a 0 = 5 * k, so n ≤ 117 / 5, which rounds to 23
    rw [hk, h117, ← mul_assoc] at hsum
    rw [mul_le_mul_iff_of_pos_right hk0] at hsum
    linarith