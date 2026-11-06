import Mathlib
/- Let $k$ be an integer greater than 1. Determine the number of positive integers $n$ such that $1 \le n \le k^2$ and the remainder of the division of $n$ by $k$ is greater than the remainder of the division of $n$ by $k+1$. Show that this number is $\frac{k(k-1)}{2}$. -/
theorem algebra_636164 (k : ℕ) (hk : k > 1) : {n : ℕ | 1 ≤ n ∧ n ≤ k ^ 2 ∧ n % k > n % (k + 1)}.ncard = k * (k - 1) / 2:= by
  -- Key insight: The set can be characterized as numbers n = k*q + r where q ≤ r, q ≥ 1, and r < k
  have h1 : {n : ℕ | 1 ≤ n ∧ n ≤ k ^ 2 ∧ n % k > n % (k + 1)} = {n : ℕ | ∃ q r : ℕ, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < k}:= by
    ext n
    constructor
    .
      -- Forward direction: If n satisfies the condition, then n = k*q + r with the required properties
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩
      -- Show that n < k² (n cannot equal k²)
      replace h2 : n < k ^ 2:= by
        have g : n ≠ k ^ 2:= by
          by_contra H
          subst n
          have g : k ∣ k ^ 2:= by
            use k
            ring
          rw [show k ^ 2 % k = 0 by exact Nat.dvd_iff_mod_eq_zero.mp g] at h3
          omega
        omega
      simp
      -- Express n in terms of quotient and remainder: n = k*q + r
      have h4:= Eq.symm (Nat.div_add_mod n k)
      set q:= n / k with hq
      set r:= n % k with hr
      clear_value q r
      -- Show that r < k (remainder property)
      have hrle : r < k:= by
        subst r
        refine Nat.mod_lt n (by omega)
      -- Show that q ≤ r (key condition)
      have h5 : q ≤ r:= by
        by_contra H
        simp at H
        have hqle : q < k:= by
          by_contra H1
          simp at H1
          replace h : k * k ≤ q * k:= by exact Nat.mul_le_mul_right k H1
          linarith
        -- Calculate n mod (k+1) when q > r
        have h5 : n % (k + 1) = (k + 1) - q + r:= by
          have h5 : (k + 1) - q + r = ((k + 1) - q + r) % (k + 1):= by
            have g : (k + 1) - q + r < k + 1:= by omega
            exact Eq.symm (Nat.mod_eq_of_lt g)
          rw [h5]
          suffices n ≡ (k + 1) - q + r [MOD k + 1] by exact this
          subst n
          suffices k * q + r + q ≡ k + 1 - q + r + q [MOD k + 1] by exact Nat.ModEq.add_right_cancel' q this
          rw [show k + 1 - q + r + q = k + 1 + r by omega]
          rw [show k * q + r + q = (k + 1) * q + r by ring]
          have g1 : (k + 1) * q ≡ k + 1 [MOD k + 1]:= by
            have g1 : (k + 1) * q ≡ 0 [MOD k + 1]:= by
              suffices k + 1 ∣ (k + 1) * q by exact Nat.modEq_zero_iff_dvd.mpr this
              simp
            have g2 : k + 1 ≡ 0 [MOD k + 1]:= by
              suffices k + 1 ∣ k + 1 by exact Nat.modEq_zero_iff_dvd.mpr this
              simp
            exact Nat.ModEq.trans g1 (id (Nat.ModEq.symm g2))
          exact Nat.ModEq.add_right r g1
        rw [h5] at h3
        omega
      -- Show that q ≥ 1 (n must be at least k)
      have h6 : q ≥ 1:= by
        by_contra H
        simp at H
        replace h5 : q = 0:= by omega
        subst q
        rw [H] at h4
        simp at h4
        subst n
        rw [show r % (k + 1) = r by refine Nat.mod_eq_of_lt (by omega)] at h3
        simp at h3
      use q, r
    .
      -- Reverse direction: If n = k*q + r with the required properties, then n satisfies the condition
      intro h
      simp at h
      rcases h with ⟨q, r, h1, h2, h3, h4⟩
      simp
      refine ⟨by omega, ?_, ?_⟩
      .
        -- Show that n ≤ k²
        replace h2 : q + 1 ≤ k:= by linarith
        replace h4 : k * q + r < k * (q + 1):= by linarith
        replace h2 : k * (q + 1) ≤ k * k:= by exact Nat.mul_le_mul_left k h2
        linarith
      .
        -- Show that n mod k > n mod (k+1)
        have hr : n % k = r:= by
          rw [show r = r % k by refine Eq.symm (Nat.mod_eq_of_lt (by omega))]
          subst n
          have g : k * q ≡ 0 [MOD k]:= by
            suffices k ∣ k * q by exact Nat.modEq_zero_iff_dvd.mpr this
            simp
          replace g : k * q + r ≡ 0 + r [MOD k]:= by exact Nat.ModEq.add_right r g
          simp at g
          exact g
        -- Express r in terms of q and a new variable r1
        set r1:= r - q with hr1
        clear_value r1
        replace hr1 : r = q + r1:= by omega
        rw [hr1] at h1
        rw [show k * q + (q + r1) = (k + 1) * q + r1 by ring] at h1
        -- Calculate n mod (k+1) = r1
        have h5 : n % (k + 1) = r1:= by
          rw [show r1 = r1 % (k + 1) by refine Eq.symm (Nat.mod_eq_of_lt (by omega))]
          subst n
          have g : (k + 1) * q ≡ 0 [MOD k + 1]:= by
            suffices k + 1 ∣ (k + 1) * q by exact Nat.modEq_zero_iff_dvd.mpr this
            simp
          replace g : (k + 1) * q + r1 ≡ 0 + r1 [MOD k + 1]:= by exact Nat.ModEq.add_right r1 g
          simp at g
          exact g
        rw [h5, hr]
        linarith
  rw [h1]
  clear h1
  -- Prove by induction that for each m < k, the count of numbers with r < m+1 is m(m+1)/2
  have h1 : ∀ m : ℕ, m < k → {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1}.ncard = m * (m + 1) / 2:= by
    intro m
    induction m with
    | zero =>
      -- Base case: m = 0, count should be 0
      intro _
      simp
      suffices {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ 1 ≤ q ∧ r = 0} = ∅ by rw [this] ; simp
      ext n
      constructor
      .
        intro h1
        simp at h1
        rcases h1 with ⟨q, r, -, h2, h3, h4⟩
        omega
      .
        simp
    | succ m ih =>
      -- Inductive step: m → m+1
      intro h
      replace ih:= ih (by omega)
      -- Split the set into two parts: r < m+1 and r = m+1
      have h1 : {n : ℕ | ∃ q r : ℕ, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1 + 1} = {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1} ∪ {n : ℕ | ∃ q : ℕ, n = k * q + (m + 1) ∧ q ≤ m + 1 ∧ q ≥ 1}:= by
        ext n
        constructor
        .
          intro h1
          simp at h1
          simp
          rcases h1 with ⟨q, r, h1, h2, h3, h4⟩
          by_cases h5 : r = m + 1
          .
            subst r
            right
            use q
          .
            left
            replace h4 : r < m + 1:= by omega
            use q, r
        .
          intro h1
          simp at h1
          rcases h1 with h1 | h1
          .
            rcases h1 with ⟨q, r, h1, h2, h3, h4⟩
            simp
            use q, r
            refine ⟨h1, h2, h3, by omega⟩
          .
            rcases h1 with ⟨q, h1, h2, h3⟩
            simp
            use q, (m + 1)
            refine ⟨h1, h2, h3, by omega⟩
      -- Show that the two sets are disjoint
      have h2 : Disjoint {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1} {n : ℕ | ∃ q : ℕ, n = k * q + (m + 1) ∧ q ≤ m + 1 ∧ q ≥ 1}:= by
        simp [Set.disjoint_iff]
        ext n
        constructor
        .
          intro h
          simp at h
          rcases h with ⟨h1, h2⟩
          rcases h2 with ⟨q2, g1, -, -⟩
          rcases h1 with ⟨q1, r, h1, -, -, h4⟩
          replace g1 : n % k = m + 1:= by
            rw [show m + 1 = (m + 1) % k by refine Eq.symm (Nat.mod_eq_of_lt (by omega))]
            rw [g1]
            have g : k * q2 ≡ 0 [MOD k]:= by
              suffices k ∣ k * q2 by exact Nat.modEq_zero_iff_dvd.mpr this
              simp
            replace g : k * q2 + (m + 1) ≡ 0 + (m + 1) [MOD k]:= by exact Nat.ModEq.add_right (m + 1) g
            simp at g
            exact g
          replace h1 : n % k = r:= by
            rw [show r = r % k by refine Eq.symm (Nat.mod_eq_of_lt (by omega))]
            rw [h1]
            have g : k * q1 ≡ 0 [MOD k]:= by
              suffices k ∣ k * q1 by exact Nat.modEq_zero_iff_dvd.mpr this
              simp
            replace g : k * q1 + r ≡ 0 + r [MOD k]:= by exact Nat.ModEq.add_right r g
            simp at g
            exact g
          rw [h1] at g1
          omega
        .
          simp
      -- Show that both sets are finite
      have h3 : {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1}.Finite ∧ {n : ℕ | ∃ q : ℕ, n = k * q + (m + 1) ∧ q ≤ m + 1 ∧ q ≥ 1}.Finite:= by
        have h3 : (Finset.range (k ^ 2) : Set ℕ).Finite:= by exact Finset.finite_toSet (Finset.range (k ^ 2))
        have h4 : {n : ℕ | ∃ q r : ℕ, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1 + 1} ⊆ Finset.range (k ^ 2):= by
          intro n hn
          simp at hn
          rcases hn with ⟨q, r, h1, h2, -, h4⟩
          replace h4 : r < k:= by omega
          replace h2 : q + 1 ≤ k:= by omega
          replace h4 : k * q + r < k * (q + 1):= by linarith
          replace h2 : (q + 1) * k ≤ k * k:= by exact Nat.mul_le_mul_right k h2
          simp
          linarith
        have h5 : {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1} ⊆ Finset.range (k ^ 2):= by
          have h5 : {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1} ⊆ {n | ∃ q r, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1 + 1}:= by
            rw [h1]
            exact Set.subset_union_left
          exact fun ⦃a⦄ a_1 => h4 (h5 a_1)
        have h6 : {n : ℕ | ∃ q : ℕ, n = k * q + (m + 1) ∧ q ≤ m + 1 ∧ q ≥ 1} ⊆ Finset.range (k ^ 2):= by
          have h6 : {n : ℕ | ∃ q : ℕ, n = k * q + (m + 1) ∧ q ≤ m + 1 ∧ q ≥ 1} ⊆ {n : ℕ | ∃ q r : ℕ, n = k * q + r ∧ q ≤ r ∧ q ≥ 1 ∧ r < m + 1 + 1}:= by
            rw [h1]
            exact Set.subset_union_right
          exact fun ⦃a⦄ a_1 => h4 (h6 a_1)
        refine ⟨by exact Set.Finite.subset h3 h5, by exact Set.Finite.subset h3 h6⟩
      -- Use the union formula for cardinality
      rw [h1, Set.ncard_union_eq h2 h3.1 h3.2, ih]
      clear ih h1 h2 h3
      -- Count the number of elements in the second set (where r = m+1)
      have h1 : ∀ t : ℕ, {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}.ncard = t:= by
        intro t
        induction t with
        | zero =>
          -- Base case: t = 0, count should be 0
          simp
          suffices {n | ∃ q, n = k * q + (m + 1) ∧ q = 0 ∧ 1 ≤ q} = ∅ by rw [this] ; simp
          ext n
          constructor
          .
            intro h1
            simp at h1
            simp
            rcases h1 with ⟨q, -, h2, h3⟩
            omega
          .
            simp
        | succ t ih =>
          -- Inductive step: t → t+1
          have h1 : {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t + 1 ∧ q ≥ 1} = insert (k * (t + 1) + (m + 1)) {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}:= by
            ext n
            constructor
            .
              intro h1
              simp at h1
              rcases h1 with ⟨q, h1, h2, h3⟩
              simp
              by_cases g : q = t + 1
              .
                left
                subst q
                exact h1
              .
                replace h2 : q ≤ t:= by omega
                right
                use q
            .
              intro h1
              simp at h1
              rcases h1 with h1 | h1
              .
                simp
                use (t + 1)
                simp
                exact h1
              .
                rcases h1 with ⟨q, h1, h2, h3⟩
                simp
                replace h2 : q ≤ t + 1:= by omega
                use q
          -- Show that the new element is not already in the set
          have h2 : (insert (k * (t + 1) + (m + 1)) {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}).ncard = {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}.ncard + 1:= by
            have h2 : (k * (t + 1) + (m + 1)) ∉ {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}:= by
              by_contra H
              simp at H
              rcases H with ⟨q, h1, h2, -⟩
              omega
            have h3 : {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1}.Finite:= by
              have h3 : (Finset.range (k * (t + 1)) : Set ℕ).Finite:= by exact Finset.finite_toSet (Finset.range (k * (t + 1)))
              have h4 : {n | ∃ q, n = k * q + (m + 1) ∧ q ≤ t ∧ q ≥ 1} ⊆ Finset.range (k * (t + 1)):= by
                intro n hn
                simp at hn
                rcases hn with ⟨q, h1, h2, -⟩
                replace h2 : k * q ≤ k * t:= by exact Nat.mul_le_mul_left k h2
                simp
                linarith
              exact Set.Finite.subset h3 h4
            exact Set.ncard_insert_of_not_mem h2 h3
          rw [ih, ←h1] at h2
          exact h2
      -- Apply the counting formula for t = m+1
      rw [h1 (m + 1)]
      rw [show (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) by ring]
      omega
  -- Apply the induction result for m = k-1
  specialize h1 (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at h1
  rw [show (k - 1) * k = k * (k - 1) by ring] at h1
  exact h1
