import Mathlib

/-
  Find all pairs of positive integers $(x, y)$, such that $x^2$ is divisible by $2xy^2 - y^3 + 1$.
-/
theorem number_theory_605383 :
  {(x, y) : ℤ × ℤ | x > 0 ∧ y > 0 ∧ (2 * x * y ^ 2 - y ^ 3 + 1) ∣ x ^ 2} =
  {(2 * k, 1) | k > 0} ∪ {(k, 2 * k) | k > 0} ∪ {(8 * k ^ 4 - k, 2 * k) | k > 0} := by

  -- we need the following lemma: if a number n is a perfect square, and
  -- (m - 1)^2 < n < (m + 1)^2 for m > 0, then n = m ^ 2
  have lem (n m : ℤ) (h : ∃ s, n = s ^ 2) (hm : m > 0) (h1 : n > (m - 1) ^ 2) (h2 : n < (m + 1) ^ 2) :
    n = m ^ 2 := by
    obtain ⟨s, rfl⟩ := h
    have s_abs_gt : |s| > |m - 1| := by exact sq_lt_sq.mp h1
    have : |m - 1| = m - 1 := by
      apply abs_eq_self.mpr
      linarith
    rw [this] at s_abs_gt
    have s_abs_lt : |s| < |m + 1| := by exact sq_lt_sq.mp h2
    have : |m + 1| = m + 1 := by
      apply abs_eq_self.mpr
      linarith
    rw [this] at s_abs_lt
    have : |s| = m := by linarith
    rw [← abs_sq, abs_pow]
    congr

  -- fix a pair (x, y)
  ext ⟨x, y⟩

  constructor
  · -- we first show the necessity
    simp
    -- if (2 * x * y ^ 2 - y ^ 3 + 1) ∣ x ^ 2, let m be such that
    -- x ^ 2 = m * (2 * x * y ^ 2 - y ^ 3 + 1)
    rintro xpos ypos ⟨m, hm⟩

    -- we need to show that in this case y ≤ 2x, which will be used to derive m > 0.
    have y_le_2x : y ≤ 2 * x := by
      by_contra! h
      let t := y - 2 * x -- if y > 2x, let t be the difference, so t ≥ 1
      have t_pos : t ≥ 1 := by
        exact Int.le_sub_left_of_add_le h

      -- take absolute value at the equation, so x ^ 2 = |2 * x * y ^ 2 - y ^ 3 + 1| * |m|
      have hm_abs : |x ^ 2| = |(2 * x * y ^ 2 - y ^ 3 + 1) * m| := by congr
      rw [abs_sq, abs_mul] at hm_abs

      -- we deduce |m| ≤ x ^ 2 as |m| is a factor of x^2
      have : |m| ∣ x ^ 2 := Dvd.intro_left |2 * x * y ^ 2 - y ^ 3 + 1| (id (Eq.symm hm_abs))
      have : |m| ≤ x ^ 2 := by
        apply Int.le_of_dvd
        apply pow_pos xpos
        exact this

      -- as x > 0, we deduce |m| ≠ 0, so |m| > 0
      have m_nz : |m| ≠ 0 := by
        by_contra! h
        have : m = 0 := by exact abs_eq_zero.mp h
        rw [this] at hm
        simp at hm
        linarith
      have m_abs_pos : |m| > 0 := by
        have : |m| ≥ 0 := by exact abs_nonneg m
        apply lt_of_le_of_ne
        exact this
        exact m_nz.symm

      -- replace y = 2x + t, we deduce the following
      have hm₁: x ^ 2 - m = -m * t * (2 * x + t) ^ 2 := by
        rw [hm]
        unfold t
        ring
      apply congrArg abs at hm₁
      rw [abs_mul, abs_mul, abs_neg] at hm₁

      -- take absolute value at hm₁,
      -- the LHS has the following upper bound
      have h_ub : |x ^ 2 - m| ≤ 2 * |x ^ 2| := by
        trans |x ^ 2| + |-m|
        · apply abs_add

        rw [abs_neg, two_mul]
        simp
        exact this
      rw [abs_sq] at h_ub
      -- the RHS is |-m * t * (2 * x + t) ^ 2| = |mt| |(2x+t^2)| ≥ 2x^2 + 1
      have h_lb : |m| * |t| * |(2 * x + t) ^ 2| ≥ 2 * x ^ 2 + 1 := by
        calc
          |m| * |t| * |(2 * x + t) ^ 2| ≥ |(2 * x + t) ^ 2| := by
            nth_rw 2 [show |(2 * x + t) ^ 2| = 1 * |(2 * x + t) ^ 2| by ring]
            have : |m| ≥ 1 := by exact m_abs_pos
            have : |t| ≥ 1 := by refine Int.one_le_abs ?h₀; linarith
            have : |m| * |t| ≥ 1 := by exact one_le_mul_of_one_le_of_one_le m_abs_pos this
            apply Int.mul_le_mul_of_nonneg_right
            exact this
            exact abs_nonneg ((2 * x + t) ^ 2)
          _ ≥ 2 * x ^ 2 + 1 := by
            simp
            rw [add_pow_two, mul_pow]
            simp
            apply le_of_sub_nonneg
            have : 4 * x ^ 2 + 2 * (2 * x) * t + t ^ 2 - (2 * x ^ 2 + 1) =
              2 * x ^ 2 + 4 * t * x + t ^ 2 - 1 := by ring
            rw [this]
            have : 2 * x ^ 2 ≥ 1 := by linarith
            have : 4 * t * x ≥ 0 := by
              apply mul_nonneg
              apply mul_nonneg
              norm_num
              exact Int.le_of_lt t_pos
              exact Int.le_of_lt xpos
            have : t ^ 2 ≥ 0 := by exact sq_nonneg t
            linarith

      -- combining the following bounds, we deduce 2 * x ^ 2 + 1 ≤ 2 * x ^ 2, which is impossible
      have : 2 * x ^ 2 + 1 ≤ 2 * x ^ 2 := by linarith
      simp at this

    -- now we showed that y ≤ 2x, so the RHS of hm is positive
    have rhs_pos : 2 * x * y ^ 2 - y ^ 3 + 1 ≥ 1 := by
      simp
      rw [show y ^ 3 = y * y ^ 2 by ring]
      apply Int.mul_le_mul_of_nonneg_right y_le_2x
      exact sq_nonneg y

    -- we then deduce m > 0.
    have m_nonneg : m ≥ 0 := by
      by_contra! h
      have : x ^ 2 < 0 := by
        rw [hm]
        apply mul_neg_of_pos_of_neg
        exact rhs_pos
        exact h
      have : x ^ 2 ≥ 0 := by exact sq_nonneg x
      linarith
    have m_nz : m ≠ 0 := by
      by_contra! h
      rw [h] at hm
      simp at hm
      linarith

    have m_pos : m > 0 := lt_of_le_of_ne m_nonneg (id (Ne.symm m_nz))

    -- now we start the analysis. the first case is y = 1
    by_cases hy : y = 1
    · -- if y = 1, we show that x = 2k.
      rw [hy] at hm
      simp at hm
      have : Even (x ^ 2) := by
        use x * m
        rw [hm]
        ring

      have : Even x := by
        by_contra! h
        have : Odd x := by exact Int.not_even_iff_odd.mp h
        have : Odd (x ^ 2) := by exact Odd.pow this
        have : ¬ Even (x ^ 2) := by exact Int.not_even_iff_odd.mpr this
        contradiction

      obtain ⟨k, hk⟩ := this
      rw [← two_mul] at hk

      left; left
      use k
      constructor
      linarith
      constructor
      exact hk.symm
      exact hy.symm

    -- now we handle the case y ≠ 1, so y > 1, i.e. y ≥ 2
    have y_ge_2 : y ≥ 2 := by
      exact lt_of_le_of_ne ypos fun a ↦ hy (id (Eq.symm a))

    -- by rearranging, we deduce the quadratic equation satisfied by x
    have h_eq_x : x ^ 2 - (2 * m * y ^ 2) * x + (m * y ^ 3 - m) = 0 := by
      rw [hm]
      ring

    -- let Δ be its discriminant
    let Δ := (2 * m * y ^ 2) ^ 2 - 4 * (m * y ^ 3 - m)
    have h_simp_Δ : Δ = 4 * m ^ 2 * y ^ 4 - 4 * m * y ^ 3 + 4 * m := by
      unfold Δ
      ring

    -- define two auxiliary constants
    let A := 4 * m * (y ^ 2 - 1) + (y - 1) ^ 2
    let B := 4 * m * (y ^ 2 + 1) - (y + 1) ^ 2

    -- we show that A and B are both positive
    have A_pos : A > 0 := by
      apply add_pos
      · apply mul_pos
        apply mul_pos (by norm_num) m_pos
        have : |y| = y := by exact abs_of_pos ypos
        simp [this]
        exact y_ge_2
      apply pow_pos
      linarith

    have B_pos : B > 0 := by
      calc
        4 * m * (y ^ 2 + 1) - (y + 1) ^ 2 ≥ 4 * (y ^ 2 + 1) - (y + 1) ^ 2 := by
          simp
          rw [show 4 * m = m * 4 by ring, mul_assoc]
          nth_rw 1 [show 4 * (y ^ 2 + 1) = 1 * (4 * (y ^ 2 + 1)) by ring]
          apply Int.mul_le_mul_of_nonneg_right
          exact m_pos
          apply mul_nonneg (by norm_num)
          refine Int.add_nonneg ?h₂.ha ?h₂.hb
          exact sq_nonneg y
          norm_num
        _ ≥ 2 * (y ^ 2 + 1) - (y + 1) ^ 2 := by
          simp
          apply mul_le_mul_of_nonneg_right
          norm_num
          refine Int.add_nonneg ?h₂.ha ?h₂.hb
        _ ≥ 1 := by
          rw [show 2 * (y ^ 2 + 1) - (y + 1) ^ 2 = (y - 1) ^ 2 by ring]
          have : y - 1 ≥ 1 := by linarith
          exact one_le_pow₀ this
        _ > 0 := by norm_num

    -- Consider Δ + A, we deduce Δ < (2 * m * y ^ 2 - y + 1) ^ 2
    have Δ_add_A : Δ + A = (2 * m * y ^ 2 - y + 1) ^ 2 := by
      unfold A Δ
      ring
    have Δ_ub : Δ < (2 * m * y ^ 2 - y + 1) ^ 2 := by linarith

    -- Consider Δ - B, we deduce Δ > (2 * m * y ^ 2 - y - 1) ^ 2
    have Δ_sub_B : Δ - B = (2 * m * y ^ 2 - y - 1) ^ 2 := by
      unfold B Δ
      ring
    have Δ_lb : Δ > (2 * m * y ^ 2 - y - 1) ^ 2 := by linarith

    -- on the other hand, Δ must be a perfect square, as witnessed by (2 * x - 2 * m * y ^ 2) ^ 2
    have : Δ = (2 * x - 2 * m * y ^ 2) ^ 2 := by
      have : x ^ 2 - 2 * m * y ^ 2 * x = -(m * y ^ 3 - m) := by linarith
      rw [mul_assoc, ← mul_sub, mul_pow, sub_pow_two]
      rw [show 2 * x * (m * y ^ 2) = 2 * m * y ^ 2 * x by ring]
      rw [this]
      unfold Δ
      ring

    -- note that 2 * m * y ^ 2 - y > 0
    have : 2 * m * y ^ 2 - y > 0 := by
      calc
        2 * m * y ^ 2 - y ≥ 2 * y ^ 2 - y := by
          simp
          rw [show 2 * m * y ^ 2 = m * (2 * y ^ 2) by ring]
          nth_rw 1 [show 2 * y ^ 2 = 1 * (2 * y ^ 2) by ring]
          apply Int.mul_le_mul_of_nonneg_right m_pos
          simp
          exact sq_nonneg y
        _ ≥ 2 * y - y := by simp; exact Int.le_self_sq y
        _ = y := by ring
        _ > 0 := by exact ypos

    -- we finally deduce Δ = (2 * m * y ^ 2 - y) ^ 2 using the lemma in the beginning
    have Δ_eq : Δ = (2 * m * y ^ 2 - y) ^ 2 := by
      apply lem
      · exact Δ_ub
      · use 2 * x - 2 * m * y ^ 2
      · exact this
      · exact Δ_lb

    -- substituting the defining equation of Δ, we deduce y ^ 2 = 4 * m
    have y_sq_eq_4m : y ^ 2 = 4 * m := by linarith

    -- so y is even
    have : Even (y ^ 2) := by use 2 * m; rw [y_sq_eq_4m]; ring
    have : Even y := by
      by_contra! h
      have : Odd y := by exact Int.not_even_iff_odd.mp h
      have : Odd (y ^ 2) := by exact Odd.pow this
      have : ¬ Even (y ^ 2) := by exact Int.not_even_iff_odd.mpr this
      contradiction

    -- and y = 2k for some k, then m = (y^2 / 4) = k^2
    obtain ⟨k, rfl⟩ := this
    have : m = k ^ 2 := by linarith
    subst this

    -- expressing y and m in terms of k, we transform the quadratic equation to (x - k) * (x - (8 * k ^ 4 - k)) = 0
    have : x ^ 2 - 2 * k ^ 2 * (k + k) ^ 2 * x + (k ^ 2 * (k + k) ^ 3 - k ^ 2) =
      (x - k) * (x - (8 * k ^ 4 - k)) := by ring
    rw [this] at h_eq_x
    simp at h_eq_x

    -- so either x = k or x = 8k^4 - k
    rcases h_eq_x with hx | hx
    · -- x = k
      have hxk : x = k := by linarith
      left; right
      use k
      constructor
      linarith
      constructor
      exact id (Eq.symm hxk)
      exact Int.two_mul k
    · -- x = 8 * k ^ 4 - k
      have hxk : x = 8 * k ^ 4 - k := by linarith
      right
      use k
      constructor
      linarith
      constructor
      exact id (Eq.symm hxk)
      exact Int.two_mul k

  · -- now we show the sufficiency
    simp
    rintro ((⟨k, kpos, rfl, rfl⟩ | ⟨k, kpos, rfl, rfl⟩) | ⟨k, kpos, rfl, rfl⟩)
    · -- case 1, (x, y) = (2k, 1) for some k
      -- then 2xy^2 - y^3 + 1 = 4k divides x^2 = 4k^2
      constructor
      linarith
      constructor
      linarith
      simp
      use k
      ring
    · -- case 2, (x, y) = (k, 2k) for some k
      -- then 2xy^2 - y^3 + 1 = 1
      constructor
      linarith
      constructor
      linarith
      rw [show 2 * k * (2 * k) ^ 2 - (2 * k) ^ 3 = 0 by ring]
      simp
    · -- case 3, (x, y) = (8k^4 - k, 2k) for some k
      -- then 2xy^2 - y^3 + 1 = 64k^6 - 16k^3 + 1, divides (8k^4 - k)^2 = 64k^8 - 16k^5 + k^2
      constructor
      have : k ^ 4 ≥ k := by
        refine le_self_pow₀ kpos ?hn
        norm_num
      linarith
      constructor
      linarith
      use k ^ 2
      ring
