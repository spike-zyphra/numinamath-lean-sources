import Mathlib

/- Determine all pairs $(x, y)$ of positive integers such that  $$ \sqrt[3]{7 x^{2}-13 x y+7 y^{2}}=|x-y|+1 $$-/

-- Custom definition of cubic root, since the standard library only has power of real index for positive numbers.
noncomputable def cubic_root (x : ℝ) : ℝ :=
  if 0 ≤ x
  then Real.rpow x (1 / 3)
  else -Real.rpow (-x) (1 / 3)

-- Show a lemma tha the cube of cubic_root of a number is equal to the number itself.
lemma cubic_root_cube (x : ℝ) : cubic_root x ^ 3 = x := by
  simp [cubic_root]
  -- Consider the cases 0 ≤ x³ and x³ < 0 respectively.
  split_ifs with hx
  . -- If 0 ≤ x³, then 0 ≤ x.
    replace hx : 0 ≤ x := by
      by_contra! hx'
      nlinarith only [hx, hx', show 0 < x ^ 2 by nlinarith only [hx']]
    rw [<-Real.rpow_natCast, <-Real.rpow_mul hx]
    norm_num
  . -- If x³ < 0, then x < 0.
    replace hx : x < 0 := by
      by_contra! hx'
      nlinarith only [hx, hx', sq_nonneg (x)]
    have (x : ℝ) : (-x) ^ 3 = -x ^ 3 := by
      ring
    rw [this, <-Real.rpow_natCast, <-Real.rpow_mul (by linarith only [hx])]
    norm_num

/- Determine all pairs $(x, y)$ of positive integers such that  $$ \sqrt[3]{7 x^{2}-13 x y+7 y^{2}}=|x-y|+1 $$-/
theorem number_theory_24464 :
    {(x, y) : ℤ × ℤ | 0 < x ∧ 0 < y ∧ cubic_root (7 * x ^ 2 - 13 * x * y + 7 * y ^ 2) = |x - y| + 1} = {(m ^ 3 + 2 * m ^ 2 - m - 1, m ^ 3 + m ^ 2 - 2 * m - 1) | m ≥ 2} ∪ {(m ^ 3 + m ^ 2 - 2 * m - 1, m ^ 3 + 2 * m ^ 2 - m - 1) | m ≥ 2} ∪ {(1, 1)} := by
  ext ⟨x, y⟩
  simp
  constructor
  . -- Suppose x, y > 0 such that cubic_root (7 * x ^ 2 - 13 * x * y + 7 * y ^ 2) = |x - y| + 1.
    rintro ⟨hx, hy, h⟩
    by_cases heq : x = y
    . -- Suppose x = y, then the expression reduces to x ^ (2 / 3) = 1.
      simp [<-heq, cubic_root] at h
      ring_nf at h
      simp [show (0 : ℝ) ≤ x ^ 2 by positivity] at h
      rw [<-Real.rpow_natCast, <-Real.rpow_mul (by positivity), show (1 : ℝ) = 1 ^ ((2 : ℕ) * 3⁻¹ : ℝ) by rw [Real.one_rpow], Real.rpow_left_inj (by positivity) (by positivity) (by positivity)] at h
      simp at h
      simp [h, <-heq]
    . -- Now x ≠ y.
      -- The first case is impossible since we assumed x ≠ y.
      have : ¬(x = 1 ∧ y = 1) := by
        by_contra!
        obtain ⟨hx, hy⟩ := this
        absurd heq
        linarith
      simp [this]
      clear this
      wlog hxy : x > y
      . -- Note that the case x < y is similar.
        specialize this y x hy hx (by rw [<-abs_neg]; ring_nf at h ⊢; exact h) (by tauto) (by push_neg at heq hxy; apply lt_of_le_of_ne hxy heq)
        obtain (⟨m, hm, hx, hy⟩ | ⟨m, hm, hx, hy⟩) := this
        . right
          use m
        . left
          use m
      . -- Now suppose that x > y.
        -- The last case is impossible, since it corresponds to the case x < y.
        have : ¬(∃ m, 2 ≤ m ∧ m ^ 3 + m ^ 2 - 2 * m - 1 = x ∧ m ^ 3 + 2 * m ^ 2 - m - 1 = y) := by
          by_contra!
          obtain ⟨m, hm, hx, hy⟩ := this
          rw [<-hx, <-hy] at hxy
          linarith [show m ^ 2 - m > 0 by nlinarith]
        simp [this]
        clear this
        -- Raise both sides of the original equation to the power of 3.
        replace h := congr_arg (· ^ 3) h
        simp [cubic_root_cube] at h
        -- Let n = x - y and simplify the expression.
        let n : ℤ := x - y
        have : (|x - y| : ℝ) = n := by
          norm_cast
          simp [le_of_lt hxy]
        rw [this, show x = y + n by simp [n]] at h
        clear this
        norm_cast at h
        -- This expression is equivalent to (2y + n)² = (n - 2)²(4n + 1).
        replace h : (2 * y + n) ^ 2 = (n - 2) ^ 2 * (4 * n + 1) := by
          linarith
        have h₀ : 0 < n := by
          simp [n, hxy]
        -- We show that n > 2.
        have h₁ : n > 2 := by
          by_contra! h₁
          interval_cases n
          . -- If n = 1, the right hand side is not a square.
            let t := (2 * y + 1).natAbs
            replace h : t ^ 2 = 5 := by
              zify
              simp [t, Int.natAbs_sq, h]
            linarith [show 2 < t by nlinarith, show t < 3 by nlinarith]
          . -- If n = 2, the right hand side is zero.
            simp at h
            linarith
        -- Show that 4n + 1 is a perfect square.
        have h₂ : IsSquare (4 * n + 1 : ℚ) := by
          use (2 * y + n) / (n - 2 : ℚ)
          field_simp [show (n - 2 : ℚ) ≠ 0 by norm_cast; linarith]
          norm_cast
          linarith [h]
        norm_cast at h₂
        -- Let 4n + 1 = (2m + 1)² for some m ≥ 0.
        obtain ⟨m'', hm⟩ := h₂
        let m' := |m''|
        rw [<-pow_two, <-sq_abs, show |m''| = m' by simp [m']] at hm
        have hm' : Odd m' := by
          rw [<-Int.odd_pow' (show 2 ≠ 0 by norm_num), <-hm, show 4 * n = 2 * (2 * n) by ring]
          simp
        obtain ⟨m, h₂⟩ := hm'
        rw [h₂] at hm
        have h₃ : m' ≥ 0 := by
          simp [m']
        -- Show that m ≥ 2.
        have h₄ : m ≥ 2 := by
          nlinarith
        -- Substitute 4n + 1 = (2m + 1)² and n = m² + m into the original equation.
        rw [hm, <-mul_pow, sq_eq_sq₀ (by positivity) (by nlinarith), show n = m ^ 2 + m by linarith] at h
        -- Recall that x = y + m² + m.
        have : x = y + (m ^ 2 + m) := by
          simp [show x = y + n by simp [n]]
          linarith
        -- Now the answer is easy.
        use m, h₄, by linarith, by linarith
  . rintro (⟨hx, hy⟩ | ⟨m, ⟨hm, hx, hy⟩⟩ | ⟨m, ⟨hm, hx, hy⟩⟩)
    . -- Show that x = y = 1 satisfies the equation.
      norm_num [hx, hy]
      simp [cubic_root]
    . -- Show that the pairs (m³ + 2m² - m + 1, m³ + m² - 2m + 1) for m ≥ 2 satisfy the equation.
      refine ⟨?_, ?_, ?_⟩
      . -- Show that m³ + 2m² - m - 1 > 0.
        calc
          _ ≤ 2 ^ 3 - 1 + 0 := by
            norm_num
          _ ≤ (m ^ 3 - 1) + (2 * m - 1) * m := by
            -- The key observation is that x = m³ - 1 + (2m - 1)m, which is clearly positivve for m ≥ 2.
            apply add_le_add
            . nlinarith [show m ^ 2 ≥ 4 by nlinarith]
            . nlinarith
          _ = x := by
            linarith
      . -- Show that m³ + m² - 2m - 1 > 0.
        calc
          _ ≤ 2 ^ 3 - 1 + 0 := by
            norm_num
          _ ≤ (m ^ 3 - 1) + (m - 2) * m := by
            -- The key observation is that y = m³ - 1 + (m - 2)m, which is clearly positivve for m ≥ 2.
            apply add_le_add
            . nlinarith [show m ^ 2 ≥ 4 by nlinarith]
            . nlinarith
          _ = y := by
            linarith
      . -- Observe that it suffices to show that the expression inside cubic root is (m² + m + 1)³.
        have : cubic_root ((m ^ 2 + m + 1) ^ 3) = |(x - y : ℝ)| + 1 := by
          simp [cubic_root, if_pos (show 0 ≤ (m ^ 2 + m + 1 : ℝ) ^ 3 by positivity)]
          rw [<-hx, <-hy, <-Real.rpow_natCast, <-Real.rpow_mul]
          push_cast
          ring_nf
          simp [abs_of_nonneg (show (0 : ℝ) ≤ m + m ^ 2 by positivity)]
          ring
          positivity
        convert this using 1
        -- Show that the expression inside cubic root is indeed (m² + m + 1)³.
        congr
        rw [<-hx, <-hy]
        norm_cast
        ring
    . -- Show that the pairs (m³ + m² - 2m + 1, m³ + 2m² - m + 1) for m ≥ 2 satisfy the equation.
      refine ⟨?_, ?_, ?_⟩
      . -- Show that m³ + m² - 2m - 1 > 0.
        calc
          _ ≤ 2 ^ 3 - 1 + 0 := by
            norm_num
          _ ≤ (m ^ 3 - 1) + (m - 2) * m := by
            -- The key observation is that y = m³ - 1 + (m - 2)m, which is clearly positivve for m ≥ 2.
            apply add_le_add
            . nlinarith [show m ^ 2 ≥ 4 by nlinarith]
            . nlinarith
          _ = x := by
            linarith
      . -- Show that m³ + 2m² - m - 1 > 0.
        calc
          _ ≤ 2 ^ 3 - 1 + 0 := by
            norm_num
          _ ≤ (m ^ 3 - 1) + (2 * m - 1) * m := by
            -- The key observation is that x = m³ - 1 + (2m - 1)m, which is clearly positivve for m ≥ 2.
            apply add_le_add
            . nlinarith [show m ^ 2 ≥ 4 by nlinarith]
            . nlinarith
          _ = y := by
            linarith
      . -- Observe that it suffices to show that the expression inside cubic root is (m² + m + 1)³.
        have : cubic_root ((m ^ 2 + m + 1) ^ 3) = |(x - y : ℝ)| + 1 := by
          simp [cubic_root, if_pos (show 0 ≤ (m ^ 2 + m + 1 : ℝ) ^ 3 by positivity)]
          rw [<-hx, <-hy, <-Real.rpow_natCast, <-Real.rpow_mul]
          push_cast
          ring_nf
          rw [<-neg_add_eq_sub, <-neg_add_rev, abs_neg]
          simp [abs_of_nonneg (show (0 : ℝ) ≤ m + m ^ 2 by positivity)]
          ring
          positivity
        convert this using 1
        -- Show that the expression inside cubic root is indeed (m² + m + 1)³.
        congr
        rw [<-hx, <-hy]
        norm_cast
        ring