import Mathlib

/- Solve the equation

$$
8 x^{3}+8 x^{2} y+8 x y^{2}+8 y^{3}=15\left(x^{2}+y^{2}+x y+1\right)
$$

in the set of integers. -/
theorem algebra_604238 :
    {(x, y) : ℤ × ℤ | 8 * x ^ 3 + 8 * x ^ 2 * y + 8 * x * y ^ 2 + 8 * y ^ 3 = 15 * (x ^ 2 + y ^ 2 + x * y + 1)} = {(1, 2), (2, 1)} := by
  -- First break the goal into two parts.
  ext ⟨x, y⟩
  apply Iff.intro
  . -- Show that the equation implies (x, y) = (1, 2) or (2, 1).
    intro h₀
    simp at h₀
    -- Transform the equation into (x² + y²)(8x + 8y - 15) = 15(xy + 1).
    replace h₀ : (x ^ 2 + y ^ 2) * (8 * x + 8 * y - 15) = 15 * (x * y + 1) := by
      linarith only [h₀]
    -- Show that 3 ∣ (x² + y²)(8x + 8y - 15).
    have h₁ : 3 ∣ (x ^ 2 + y ^ 2) * (8 * x + 8 * y - 15) := by
      rw [h₀]
      apply dvd_mul_of_dvd_left
      norm_num
    -- A small technical lemma.
    have lm : ∀ a : ℤ, a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
      omega
    -- Show that 3 ∤ x² + y².
    have h₂ : ¬3 ∣ x ^ 2 + y ^ 2 := by
      -- Assume on the contrary that 3 ∣ x² + y².
      by_contra! h₂
      -- Show that any square modulo 3 is either 0 or 1.
      have h3residue : ∀ a : ℤ, a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
        intro a
        rcases lm a with (h | h | h)
        <;> simp [h, pow_two, Int.mul_emod, Int.add_emod]
      -- By listing all possibilities, show that x ^ 2 ≡ y ^ 2 ≡ 0 (mod 3).
      have h₃ : (x ^ 2 % 3 = 0) ∧ (y ^ 2 % 3 = 0) := by
        rcases h3residue x with (h1 | h1)
        all_goals
          rcases h3residue y with (h2 | h2)
          all_goals
            omega
      clear h3residue
      -- Now we have 3 ∣ x² and 3 ∣ y², hence 3 ∣ x and 3 ∣ y.
      have hx := Int.dvd_of_emod_eq_zero h₃.1
      have hy := Int.dvd_of_emod_eq_zero h₃.2
      replace hx := Int.Prime.dvd_pow (Nat.prime_three) hx
      zify at hx
      simp at hx
      replace hy := Int.Prime.dvd_pow (Nat.prime_three) hy
      zify at hy
      simp at hy
      -- We will have 9 ∣ x² + y².
      have h₄ : 3 ^ 2 ∣ x ^ 2 + y ^ 2 := by
        apply Int.dvd_add
        . apply pow_dvd_pow_of_dvd hx
        . apply pow_dvd_pow_of_dvd hy
      -- Then we have 3 ∣ xy + 1.
      have h₅ : 3 ∣ x * y + 1 := by
        apply @Int.dvd_of_mul_dvd_mul_right 3 _ _ (by norm_num)
        rw [<-pow_two]
        apply @Int.dvd_of_dvd_mul_right_of_gcd_one _ 5 _ _ (by norm_num)
        calc
          3 ^ 2 ∣ x ^ 2 + y ^ 2 := h₄
          _ ∣ 15 * (x * y + 1) := by
            rw [<-h₀]
            apply dvd_mul_right
          _ = 5 * ((x * y + 1) * 3) := by
            ring
      -- Since 3 ∣ xy, it is a contradiction.
      replace h₅ : (3 : ℤ) ∣ 1 := by
        rw [<-@Int.dvd_add_right _ (x * y)]
        exact h₅
        calc
          3 ∣ x := hx
          _ ∣ x * y := by
            apply Int.dvd_mul_right
      omega
    -- We have 3 ∣ x + y because 3 ∣ (x² + y²)(8x + 8y - 15) and 3 ∤ x² + y².
    have h₃ : 3 ∣ x + y := by
      apply Int.Prime.dvd_mul' (Nat.prime_three) at h₁
      simp [h₂] at h₁
      have h₃ := Int.dvd_iff_dvd_of_dvd_sub h₁
      norm_num at h₃
      rw [<-mul_add] at h₃
      apply Int.Prime.dvd_mul' (Nat.prime_three) at h₃
      norm_num at h₃
      exact h₃
    -- By listing all possibilities, show that x ≡ 1 and y ≡ 2, or y ≡ 1 and x ≡ 2 (mod 3).
    have h₄ : (x % 3 = 1 ∧ y % 3 = 2) ∨ (x % 3 = 2 ∧ y % 3 = 1) ∨ (x % 3 = 0 ∧ y % 3 = 0) := by
      rcases lm x with (h1 | h1 | h1)
      all_goals
        rcases lm y with (h2 | h2 | h2)
        all_goals
          omega
    have h₄' : ¬(x % 3 = 0 ∧ y % 3 = 0) := by
      by_contra!
      obtain ⟨h₅, h₆⟩ := this
      simp at h₅ h₆
      replace h₅ := pow_dvd_pow_of_dvd h₅ 2
      replace h₆ := pow_dvd_pow_of_dvd h₆ 2
      have h₇ : 3 ∣ x ^ 2 + y ^ 2 := by
        calc
          (3 : ℤ) ∣ 3 ^ 2 := by norm_num
          _ ∣ x ^ 2 + y ^ 2 := by
            apply Int.dvd_add
            . exact h₅
            . exact h₆
      contradiction
    simp only [h₄'] at h₄
    simp at h₄
    clear h₄'
    -- WLOG, assume that x ≡ 1 and y ≡ 2 (mod 3).
    wlog h₅ : x % 3 = 1 ∧ y % 3 = 2
    . simp [h₅] at h₄
      specialize this y x (by linarith only [h₀]) (by rw [add_comm]; nth_rw 2 [add_comm] at h₁; exact h₁) lm (by rw [add_comm] at h₂; exact h₂) (by rw [add_comm] at h₃; exact h₃) (by simp [h₄]) (by simp [h₄])
      simp at this ⊢
      tauto
    . -- Now x ≡ 1 and y ≡ 2 (mod 3).
      clear h₄
      -- Show that x = 3a + 1 and y = 3b + 2.
      have h₆ := Int.ediv_add_emod x 3
      have h₇ := Int.ediv_add_emod y 3
      rw [h₅.1] at h₆
      rw [h₅.2] at h₇
      generalize h₈ : x / 3 = a
      generalize h₉ : y / 3 = b
      rw [h₈] at h₆
      rw [h₉] at h₇
      -- -- Substituting x = 3a + 1 and y = 3b + 2 into the original equation.
      rw [show 8 * x + 8 * y - 15 = (8 * (a + b) + 3) * 3 by rw [<-h₆, <-h₇]; ring] at h₀
      have h₀' := h₀
      rw [show x * y + 1 = 3 * (3 * a * b + 2 * a + b + 1) by rw [<-h₆, <-h₇]; ring] at h₀
      nth_rw 2 [<-mul_assoc] at h₀
      -- Show that 3 ∣ 8(a + b) + 3.
      have h₁₀ : 3 ∣ 8 * (a + b) + 3 := by
        apply Int.dvd_of_mul_dvd_mul_right (show 3 ≠ 0 by norm_num)
        suffices 3 * 3 ∣ 15 * 3 * (3 * a * b + 2 * a + b + 1) by
          rw [<-h₀] at this
          apply @Int.dvd_of_dvd_mul_right_of_gcd_one _ (x ^ 2 + y ^ 2) _ this
          rw [Int.gcd_eq_one_iff_coprime, <-pow_two]
          apply IsCoprime.pow_left
          rw [<-Int.gcd_eq_one_iff_coprime, Int.gcd_eq_natAbs, <-Nat.Coprime.gcd_eq_one]
          simp
          rw [Nat.Prime.coprime_iff_not_dvd]
          zify
          simp [show 0 ≤ x ^ 2 + y ^ 2 by positivity, h₂]
          exact Nat.prime_three
        norm_num
        rw [mul_comm, show (45 : ℤ) = 5 * 9 by rfl, <-mul_assoc]
        apply Int.dvd_mul_left
      -- Now 3 ∣ a + b.
      replace h₁₀ : 3 ∣ a + b := by
        rw [Int.dvd_add_left (by norm_num)] at h₁₀
        apply Int.Prime.dvd_mul' (Nat.prime_three) at h₁₀
        omega
      -- Distinguish two cases: a + b = 0 or a + b ≠ 0.
      by_cases h₁₁ : a + b = 0
      . -- Suppose a + b = 0. Substitute x = 3a + 1, y = 3b + 1 and b = -a into the original equation.
        rw [<-h₆, <-h₇, show b = -a by linarith only [h₁₁]] at h₀
        -- Now a(3a - 1) = 0.
        have h₁₂ : a * (3 * a - 1) = 0 := by
          linarith only [h₀]
        simp at h₁₂
        -- Since a has to be an integer, a = 0.
        replace h₁₂ : a = 0 := by
          omega
        simp [h₁₂] at h₆ h₁₁
        simp [h₁₁] at h₇
        simp
        tauto
      . -- Now suppose that a + b ≠ 0.
        have h₁₂ : |8 * (a + b) + 3| + 3 ≥ 24 := by
          calc
            |8 * (a + b) + 3| + 3 ≥ |8 * (a + b) + 3 - 3| := by
              -- Use the triangle inequality.
              apply abs_add
            _ = 8 * |a + b| := by
              simp [abs_mul]
            _ ≥ 8 * 3 := by
              -- Since a + b ≠ 0 and 3 ∣ a + b, |a + b| ≥ 3.
              rw [dvd_iff_exists_eq_mul_left] at h₁₀
              obtain ⟨k, h₁₀⟩ := h₁₀
              rw [ge_iff_le, mul_le_mul_left (by norm_num), h₁₀]
              simp [abs_mul]
              by_contra this
              simp at this
              omega
            _ = 24 := by rfl
        -- Now we have |(x² + y²)(8(a + b) + 3)| ≥ 21(x² + y²) > 5|xy + 1|, contradicting the assumption.
        have h₁₃ : 15 * |x * y + 1| > 15 * |x * y + 1| := by
          calc
            15 * |x * y + 1| = |15 * (x * y + 1)| := by
              simp [abs_mul]
            _ = |(x ^ 2 + y ^ 2) * ((8 * (a + b) + 3) * 3)| := by
              rw [<-h₀']
            _ = |(x ^ 2 + y ^ 2)| * (|8 * (a + b) + 3| * 3) := by
              simp [abs_mul]
            _ ≥ |(x ^ 2 + y ^ 2)| * (21 * 3) := by
              -- Use the fact that |8(a + b) + 3| + 3 ≥ 24 proved above.
              apply Int.mul_le_mul_of_nonneg_left
              linarith only [h₁₂]
              positivity
            _ > |(x ^ 2 + y ^ 2) * 2| * 30 := by
              simp [abs_mul]
              rw [mul_assoc]
              rw [mul_lt_mul_left]
              norm_num
              by_contra!
              simp at this
              omega
            _ ≥ (4 * |x * y|) * 30 := by
              rw [ge_iff_le, mul_le_mul_right (by norm_num)]
              -- Use the fact that x² + y² ≥ 2|x||y|, which is basically the AM-GM inequality.
              have := sq_nonneg (|x| - |y|)
              rw [sub_sq, sq_abs, sq_abs, mul_assoc, <-abs_mul] at this
              rw [abs_of_nonneg (show 0 ≤ (x ^ 2 + y ^ 2) * 2 by positivity)]
              linarith only [this]
            _ ≥ (2 * |x * y| + 2) * 30 := by
              rw [ge_iff_le, mul_le_mul_right (by norm_num)]
              -- Use the fact that |x * y| ≥ 1.
              suffices |x * y| ≥ 1 by
                linarith only [this]
              by_contra!
              simp at this
              omega
            _ = (|x * y| + 1) * 60 := by
              ring
            _ > (|x * y| + 1) * 15 := by
              rw [gt_iff_lt, mul_lt_mul_left (by positivity)]
              norm_num
            _ ≥ (|x * y + 1|) * 15 := by
              rw [ge_iff_le, mul_le_mul_right (by norm_num)]
              apply abs_add
            _ = 15 * (|x * y + 1|) := by
              ac_rfl
        linarith only [h₁₃]
  . -- Show that (x, y) = (1, 2) or (2, 1) satisfies the equation.
    intro hxy
    simp at hxy
    obtain ⟨hx, hy⟩ | ⟨hx, hy⟩ := hxy
    <;> simp [hx, hy]
  