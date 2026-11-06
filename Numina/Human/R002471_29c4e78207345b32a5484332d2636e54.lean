import Mathlib

open Real

/- Let a and b be positive real numbers with a ≥ b. Let ρ be the maximum possible value of a/b​  for which the system of equations a^2+y^2=b^2+x^2=(a−x)^2+(b−y)^2 has a solution in (x,y) satisfying 0 ≤ x < a and 0 ≤ y < b. Then ρ^2 can be expressed as a fraction, where m and n are relatively prime positive integers. Find m + n
-/
theorem algebra_93921 (m n : ℕ) (hm : 0 < m) (hn: 0 < n) (hmn: Nat.Coprime m n)
(ρ : ℝ) (hρ : IsGreatest {a / b | (a : ℝ) (b : ℝ) (x : ℝ) (y : ℝ) (_ : 0 < b) (_ : 0 < a) (_ : b ≤ a) (_ : 0 ≤ x) (_ : x < a) (_ : 0 ≤ y) (_ : y < b) (_ : a^2 + y^2 = b^2 + x^2) (_ : b^2 + x^2 = (a-x)^2 + (b-y)^2)}
 ρ) (hrmn : ρ^2 = m / n) : m + n = 7 := by
    -- we'll first prove ρ is 2/√3 by proving that is the greatest value of the set
    have hρ_val : ρ = 2 / √3 := by
      apply IsGreatest.unique hρ
      constructor
      -- first use a = 1, b = √3/2, x = 1/2, y=0 to show 2/√3 is in the set
      . use 1, √3/2, 1/2, 0
        have : 0 < √3/2 := by
          calc
            0 = 0/2 := by norm_num
            _ < √3/2 := by refine div_lt_div_of_pos_right ?_ ?_ <;> simp
        use (by linarith)
        use (by norm_num)
        have : √3/2 ≤ 1 := by
          calc
            √3/2 ≤ √4/2 := by refine div_le_div_of_nonneg_right ?_ ?_ <;> simp; norm_num
            _ = √(2^2)/2 := by norm_num
            _ = 1 := by simp
        use this, (by norm_num), (by norm_num), (by norm_num), (by assumption)
        use (by
          norm_num
          calc
            1 = 3/4 + 1/4 := by norm_num
            _ = (√3)^2/2^2 + 1/4 := by congr <;> first|simp|norm_num
            _ = (√3 / 2) ^ 2 + 1 / 4 := by ring
        )
        use (by
          norm_num
          ring
        )
        use (by field_simp)
      -- next assume a, b, x, y from the set, we'll prove 2/√3 is an upper bound
      . intro r hr
        obtain ⟨a, b, x, y, hr⟩ := hr
        obtain ⟨hb_pos, ha_pos, hab, hx_nonneg, hax, hy_nonneg, hyb, heq₁, heq₂, hrab⟩ := hr
        ring_nf at heq₂
        -- by linear manipulation of sets we get a^2 + y^2 = 2(ax+by) = b^2+x^2
        have heq₃ : a^2 + y^2 = 2 * (a*x + b*y) := by linarith
        have heq₄ : b^2 + x^2 = 2 * (a*x + b*y) := by linarith
        -- y^2 ≤ 2by due to y ≤ b
        have hyb' : y^2 ≤ 2*b*y := by
          calc
            y^2 = y*y := by ring
            _ ≤ y*b := by
              refine mul_le_mul_of_nonneg ?_ ?_ hy_nonneg ?_
              all_goals linarith
            _= 1*(b*y) := by ring
            _ ≤ 2*(b*y) := by
              refine mul_le_mul_of_nonneg ?_ ?_ ?_ ?_
              any_goals linarith
              simp [hb_pos]
              assumption
            _ = 2*b*y := by ring
        -- this means ax ≤ a^2/2 from the last equations and consequently x ≤ a/2
        have hax : a*x ≤ a*(a/2) := by linarith
        have ha' : x ≤ a / 2 := by exact le_of_mul_le_mul_left hax ha_pos
        -- a^2 ≤ a^2+y^2 so we get a^2 ≤ b^2 + a^2/4
        have : a^2 ≤ b^2 + a^2/4 := by
          calc
            a^2 ≤ a^2 + y^2 := by simp [sq_nonneg]
            _ = b^2 + x^2 := by rw [heq₁]
            _ ≤ b^2 + a^2/4 := by
              simp
              calc
                x^2 ≤ (a/2)^2 := by exact pow_le_pow_left₀ hx_nonneg ha' 2
                _ = a^2/4 := by ring
        -- from this we get a * √3 ≤ 2 * b, and hence ρ ≤ 2/√3
        have : (a * √3)^2 ≤ (2 * b)^2 := by
          ring_nf
          simp [this]
          linarith
        have : a * √3 ≤ 2 * b := by apply nonneg_le_nonneg_of_sq_le_sq <;> linarith
        calc
          r = a / b := by rw [← hrab]
          _ = a * √ 3 / (√ 3 * b) := by field_simp; ring
          _ ≤ 2 * b /  (√ 3 * b) := by
            refine (div_le_div_iff_of_pos_right ?_).mpr this
            simp
            assumption
          _ = 2 * b / b / √ 3 := by ring
          _ = 2 / √3 := by field_simp
    -- using value of ρ, prove ρ^2 = 4/3
    have hρ_sqval : ρ^2 = 4 / 3 := by
      calc
        ρ^2 = (2/√3)^2 := by rw [hρ_val]
        _ = 4 / (√3)^2 := by ring
        _ = 4 / 3 := by simp
    rw [hρ_sqval] at hrmn
    -- finally prove m = 4 and n = 3
    have : (m: ℚ)/n = 4 / 3 := by rify; exact hrmn.symm
    have : (m:ℤ) = 4 ∧ (n:ℤ) = 3 := by
      apply Rat.div_int_inj
      any_goals linarith
      any_goals assumption
      any_goals norm_cast
    norm_cast at this
    rw [this.left, this.right]