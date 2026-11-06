import Mathlib

/- Let $N_{max}$ be a positive integer. Let $S$ be the set of all possible values for the average $(a+b)/2$, where $a$ and $b$ are distinct positive integers both less than $N_{max}$ such that $a^2$ and $b^2$ have the same last two digits. (Single-digit squares are considered to have a leading zero, e.g., $2^2$ ends with 04.)
Show that $S = \{ A \in \mathbb{N} \mid \exists D \in \mathbb{N} \text{ such that } D \ge 1, A > D, A+D < N_{max}, \text{ and } AD \text{ is a multiple of } 25 \}$. -/
theorem number_theory_635861 (N : ℕ) (hN : 0 < N) :
    {x : ℕ | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ≠ b ∧ a < N ∧ b < N ∧
      (a ^ 2 ≡ b ^ 2 [MOD 100]) ∧ 2 ∣ a + b ∧ x = (a + b) / 2} =
    {x : ℕ | ∃ D : ℕ, 1 ≤ D ∧ x > D ∧ x + D < N ∧ 25 ∣ D * x} :=
by
  ext A
  constructor
  . intro h
    simp at *
    rcases h with ⟨a, apos, b, bpos, anb, au, bu, H, evab, xeq⟩
    simp [Nat.ModEq] at H
    zify at H
    change _ ≡ _ [ZMOD _] at H
    -- Define s' and d'
    let s' : ℤ := a + b
    let d' : ℤ := a - b
    have H' : (s' * d') % 100 = 0 := by
      simp [s', d']
      ring_nf
      simp [Int.ModEq] at H
      omega

    -- Note here we show that s' and d' are same parity.
    have : Even s' ↔ Even d' := by
      have : Even a ↔ Even b := by
        have : Even (a + b) := (even_iff_exists_two_nsmul (a + b)).mpr evab
        exact Nat.even_add.mp this
      simp [s', d']
      constructor
      . intro ⟨n,hn⟩
        use n - b
        linarith
      . intro ⟨n,hn⟩
        use n + b
        linarith
    -- And they must be even!
    have evs' : Even s' := by
      have : Even (s' * d') := by
        have : 2 ∣ s'*d' := by omega
        exact (even_iff_exists_two_nsmul (s' * d')).mpr this
      have : Even s' ∨ Even d' := by
        exact Int.even_mul.mp this
      tauto
    have evd' : Even d' := by tauto
    -- So that they can be divied by two , and assign to new varible.
    let A := s' / 2
    let D' := d' / 2
    have : 100 ∣ 4 * A * D' := by
      simp [A, D']
      have : 4 * (s' / 2) * (d' / 2) = s' * d' := by
        qify
        rw [Int.cast_div, Int.cast_div]
        ring_nf
        all_goals try apply even_iff_two_dvd.mp
        all_goals tauto
      rw [this]
      omega
    -- eliminate the 4 factor at both sides.
    have : 25 ∣ A * D' := by
      rw [show (100 : ℤ) = 4 * 25 by norm_num] at this
      rw [mul_assoc] at this
      apply Int.dvd_of_mul_dvd_mul_left ?_ this
      simp
    use D'.natAbs
    constructor
    . simp [D']
      by_contra h
      simp at h
      have : d' = 0 := by
        qify at h ⊢
        rw [Int.cast_div] at h
        linarith [this]
        exact even_iff_two_dvd.mp evd'
        simp
      field_simp [d'] at this
      have : a = b := by omega
      tauto
    constructor
    . simp [xeq, D']
      qify
      rw [Int.cast_div, Int.cast_div]
      simp [d']
      by_cases h : a ≥ b
      . have : (a - b : ℚ) / 2 > 0 := by
          field_simp
          omega
        have : ∀ a : ℚ, a > 0 → |a| = a := by
          intro a ap
          simp
          linarith
        rw [this]
        have : (a - b : ℚ) < a + b := by
          norm_cast
          omega
        exact (div_lt_div_iff_of_pos_right rfl).mpr this
        simp
        omega
      . have : (a - b : ℚ) / 2 < 0 := by
          refine div_neg_of_neg_of_pos ?_ rfl
          field_simp
          omega
        have : ∀ a : ℚ, a < 0 → |a| = - a := by
          intro a ap
          simp
          linarith
        rw [this]
        field_simp
        have : (↑b - ↑a : ℚ) < (↑a + ↑b) := by
          qify at apos
          linarith
        exact (div_lt_div_iff_of_pos_right rfl).mpr this
        assumption
      . simp [s'] at evs'
        exact Int.natAbs_dvd_natAbs.mp evab
      . simp
      . exact even_iff_two_dvd.mp evd'
      . simp
    constructor
    . simp [D', d', xeq]
      have : (a + b) / 2 + ((↑a - ↑b : ℤ) / 2).natAbs = max a b := by
        by_cases h : a ≥ b
        · have : max a b = a := by
            apply max_eq_left
            linarith
          omega
        · have : max a b = b := by
            apply max_eq_right
            linarith
          omega
      rw [this]
      simp
      constructor
      <;> assumption
    . rw [xeq]
      simp [A, s'] at this
      have : D'.natAbs * ((a + b) / 2) = (D' * ((a + b) / 2)).natAbs := by
        rw [Int.natAbs_mul]
        simp
        left
        rfl
      rw [this]
      have : (25 : ℤ) ∣ (D' * ((↑a + ↑b) / 2)).natAbs := by
        apply Int.dvd_natAbs.mpr
        rw [mul_comm]
        assumption
      norm_cast at this
  . intro h
    rcases h with ⟨D, Dpos, xD, xDN, dvdDx⟩
    simp
    use A + D
    constructor
    . omega
    use A - D
    constructor
    . omega
    constructor
    . omega
    constructor
    . omega
    constructor
    . omega
    constructor
    . simp [Nat.ModEq]
      zify
      rw [Nat.cast_sub]
      have : ((↑A + ↑D) ^ 2 - (↑A - ↑D) ^ 2 : ℤ) % 100 = 0 := by
        ring_nf
        rw [show (100 : ℤ) = 4 * 25 by simp]
        field_simp
        rw [mul_comm]
        apply Int.mul_dvd_mul_right
        rw [mul_comm]
        norm_cast
      omega
      omega
    constructor
    . zify
      rw [Nat.cast_sub]
      ring_nf
      omega
      omega
    . zify
      rw [Nat.cast_sub]
      simp
      omega
      omega
