import Mathlib
/- 4. If $k$ is an integer such that the equation in $x$
$$
k x^{2}-(2 k+3) x+3=0
$$

has rational roots, then $k$ is called a "good number". Then, the number of good numbers $k$ is $(\quad)$.
(A) 0
(B) 1
(C) 2
(D) 3 -/
theorem number_theory_199432 : {k : ℤ | ∃ x : ℚ, k * x ^ 2 - (2 * k + 3) * x + 3 = 0}.ncard = 3:= by
  -- First, we prove that the set of good numbers is exactly {0, 2, -2}
  have h1 : {k : ℤ | ∃ x : ℚ, k * x ^ 2 - (2 * k + 3) * x + 3 = 0} = {0, 2, -2}:= by
    ext k
    constructor
    -- Forward direction: if k is a good number, then k ∈ {0, 2, -2}
    .
      intro h
      simp at h
      rcases h with ⟨x, h⟩
      -- Case analysis: k = 0 or k ≠ 0
      by_cases hk : k = 0
      -- Case 1: k = 0
      .
        subst k
        simp
      -- Case 2: k ≠ 0
      .
        -- If k ≠ 0, then x ≠ 0 (otherwise the equation becomes -3 = 0)
        have hx : x ≠ 0:= by
          by_contra H
          subst x
          simp at h
        -- Transform the equation to show that 4k² + 9 is a perfect square
        replace hx : 4 * k ^ 2 + 9 = (x * k - 3 / x) ^ 2:= by
          field_simp
          ring_nf
          -- Rearrange the original equation
          replace h : k * x ^ 2 = (2 * k + 3) * x - 3:= by linarith
          rw [show k ^ 2 * x ^ 4 = (k * x ^ 2) ^ 2 by ring_nf]
          rw [show k ^ 2 * x ^ 2 = k * (k * x ^ 2) by ring_nf]
          rw [h]
          ring_nf
          rw [show k ^ 2 * x ^ 2 = k * (k * x ^ 2) by ring_nf]
          rw [h]
          ring_nf
        -- Lemma: if a natural number has a rational square root, then it has an integer square root
        have h1 : ∀ a : ℕ, (∃ r : ℚ, √a = r) → ∃ t : ℕ, √a = t:= by
          intro a h
          rcases h with ⟨r, hr⟩
          have h2:= Rat.mul_self_den r
          have h:= hr
          replace hr : √a ^ 2 = r ^ 2:= by rw [hr]
          field_simp at hr
          replace hr : a = r ^ 2:= by rify ; linarith
          have g2 : (↑a : ℚ).den = 1:= by exact rfl
          rw [show r * r = r ^ 2 by ring_nf] at h2
          rw [hr, h2] at g2
          simp at g2
          rw [show r = r.num / r.den by exact Eq.symm (Rat.num_div_den r)] at h
          rw [g2] at h
          simp at h
          use (r.num).natAbs
          rw [show (↑(r.num).natAbs : ℝ) = (↑(r.num).natAbs : ℤ) by exact rfl]
          simp
          rw [h]
          rw [abs_of_nonneg (by rw [←h] ; positivity)]
        -- Apply the lemma to show that 4k² + 9 has an integer square root
        specialize h1 (4 * k ^ 2 + 9).natAbs ?_
        use |x * k - 3 / x|
        set a:= 4 * k ^ 2 + 9 with ha
        set r:= x * k - 3 / x
        clear_value a r
        qify at ha
        rw [←ha] at hx
        rw [show (↑(a.natAbs) : ℝ) = (↑(↑(a.natAbs) : ℤ) : ℝ) by rfl]
        simp
        rify at hx
        rw [hx]
        rw [show |(↑r : ℝ) ^ 2| = |(↑r : ℝ)| ^ 2 by field_simp]
        set t:= |(↑r : ℝ)| with ht
        clear_value t
        replace ht : t ≥ 0:= by subst t ; positivity
        field_simp
        -- Now we have that 4k² + 9 = t² for some natural number t
        rcases h1 with ⟨t, ht⟩
        set a:= 4 * k ^ 2 + 9 with ha
        clear_value a
        rw [show (↑(a.natAbs) : ℝ) = (↑(↑(a.natAbs) : ℤ) : ℝ) by rfl] at ht
        simp at ht
        replace ht : √|a| ^ 2 = t ^ 2:= by rw [ht]
        field_simp at ht
        subst a
        simp at ht
        rw [abs_of_pos (by positivity)] at ht
        set k1:= k.natAbs with hk1
        clear_value k1
        replace ht : 4 * k1 ^ 2 + 9 = t ^ 2:= by
          subst k1
          rify
          field_simp
          exact ht
        -- Case analysis on the size of |k|
        by_cases hk2 : k1 ≤ 2
        -- If |k| ≤ 2, check each case
        .
          replace hk2 : k1 = 0 ∨ k1 = 1 ∨ k1 = 2:= by omega
          rcases hk2 with hk2 | hk2 | hk2
          -- |k| = 0 contradicts k ≠ 0
          .
            subst k1
            simp at hk2
            trivial
          -- |k| = 1: 4·1² + 9 = 13 is not a perfect square
          .
            subst k1
            rw [hk2] at ht
            simp at ht
            replace ht : IsSquare 13:= by
              use t
              linarith
            absurd ht
            native_decide
          -- |k| = 2: 4·2² + 9 = 25 = 5², so k = ±2
          .
            subst k1
            zify at hk2
            replace hk2 : k = 2 ∨ k = -2:= by exact abs_eq_abs.mp hk2
            rcases hk2 with hk2 | hk2
            all_goals
              subst k
              simp
        -- If |k| ≥ 3, show this leads to a contradiction
        .
          replace hk2 : k1 ≥ 3:= by omega
          -- For |k| ≥ 3, we have 2|k| < t < 2|k| + 1, which is impossible for integers
          have ht1 : t > 2 * k1:= by
            by_contra H
            simp at H
            replace H : t ^ 2 ≤ (2 * k1) ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
            linarith
          have ht2 : t < 2 * k1 + 1:= by
            by_contra H
            simp at H
            replace H : t ^ 2 ≥ (2 * k1 + 1) ^ 2:= by exact Nat.pow_le_pow_of_le_left H 2
            linarith
          omega
    -- Backward direction: if k ∈ {0, 2, -2}, then k is a good number
    .
      intro h
      simp at h
      rcases h with h | h | h
      -- k = 0: equation becomes -3x + 3 = 0, so x = 1
      .
        subst k
        simp
        use 1
        simp
      -- k = 2: equation becomes 2x² - 7x + 3 = 0, so x = 3
      .
        subst k
        simp
        use 3
        norm_num
      -- k = -2: equation becomes -2x² + x + 3 = 0, so x = -1
      .
        subst k
        simp
        use -1
        norm_num
  -- Apply the characterization to conclude the cardinality is 3
  rw [h1]
  norm_num
