import Mathlib

/- Vind alle paren $(x, y)$ van gehele getallen die voldoen aan

$$
x^{2}+y^{2}+3^{3}=456 \sqrt{x-y} .
$$ -/
theorem number_theory_604517 :
    {(x, y) : ℤ × ℤ | x ^ 2 + y ^ 2 + 3 ^ 3 = 456 * Real.sqrt (x - y)} = {(30, 21), (-21, -30)} := by
  -- Simplify the goal into two parts.
  rw [Set.ext_iff]
  intro (x, y)
  simp
  apply Iff.intro
  . -- The equation implies (x, y) = (30, 21) or (-21, -30).
    intro h
    -- Show that √(x - y) ≠ 0, hence x - y ≥ 0.
    have h₀ : Real.sqrt (x - y : ℤ) ≠ 0 := by
      intro h₀
      simp at h₀
      rw [h₀] at h
      linarith only [h, show 0 < (x : ℝ) ^ 2 + y ^ 2 + 3 ^ 3 by positivity]
    simp [Real.sqrt_ne_zero'] at h₀
    -- Show that √(x - y) is rational, because it equals (x² + y² + 3³) / 456.
    have h₁ : ¬Irrational (Real.sqrt (x - y : ℤ)) := by
      simp [Irrational]
      use (x ^ 2 + y ^ 2 + 3 ^ 3 : ℚ) / 456
      simp
      rw [div_eq_iff (by norm_num), mul_comm, h]
    -- Show that (x - y) is a perfect square, write it as r'².
    rw [irrational_sqrt_intCast_iff_of_nonneg (by omega)] at h₁
    simp at h₁
    obtain ⟨r', h₁⟩ := h₁
    rw [<-pow_two] at h₁
    -- Let r = |r'|.
    let r := |r'|
    rw [show r' ^ 2 = r ^ 2 by rw [sq_abs]] at h₁
    -- Now r is defined in such a way that 0 ≤ r.
    have hr : 0 ≤ r := by
      simp [r]
    clear_value r
    -- Substitute r = √(x - y) into the original equation.
    rw [show (x - y : ℝ) = (r : ℤ) ^ 2 by norm_cast, Real.sqrt_sq (by simp [hr])] at h
    -- Restrcict the consideration to integers.
    norm_num at h
    norm_cast at h
    -- Show that (x ^ 2 + y ^ 2) % 3 = 0, i.e., 3 ∣ x² + y².
    have h₂ := congr_arg (· % 3) h
    simp at h₂
    rw [Int.add_emod, Int.mul_emod] at h₂
    norm_num at h₂
    apply Int.emod_eq_zero_of_dvd at h₂
    -- Show that any square modulo 3 is either 0 or 1.
    have h3residue : ∀ a : ℤ, a ^ 2 % 3 = 0 ∨ a ^ 2 % 3 = 1 := by
      intro a
      have : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by
        omega
      rcases this with (h | h | h)
      <;> simp [h, pow_two, Int.mul_emod, Int.add_emod]
    -- By listing all possibilities, show that x ^ 2 ≡ y ^ 2 ≡ 0 [MOD 3].
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
    -- Let x = 3a and y = 3b.
    rw [dvd_iff_exists_eq_mul_right] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    rw [ha, hb] at h₁
    -- Since 3a - 3b = x - y = r², we have 3 ∣ r².
    have h₄ : 3 ∣ r ^ 2 := by
      rw [<-h₁, <-mul_sub]
      apply dvd_mul_right
    -- Since 3 ∣ r², we have 3 ∣ r.
    replace h₄ : 3 ∣ r := by
      apply Int.Prime.dvd_pow (Nat.prime_three) at h₄
      zify at h₄
      simp_all
    -- Write r = 3c.
    rw [dvd_iff_exists_eq_mul_right] at h₄
    obtain ⟨c, h₄⟩ := h₄
    rw [h₄, mul_pow, show (3 ^ 2 : ℤ) = 3 * 3 by norm_num, <-mul_sub, mul_assoc] at h₁
    -- Let a - b = 3c².
    rw [mul_right_inj' (by norm_num)] at h₁
    -- Substitute a = b + 3c² into the original equation to get 2b² + 6c²b + (9c⁴ + 3 - 152c) = 0, and completing the square to get (2b + 3c²)² + (9c⁴ + 6 - 304c) = 0.
    apply eq_add_of_sub_eq at h₁
    rw [h₄, ha, h₁, hb] at h
    replace h₀ : (2 * b + 3 * c ^ 2) ^ 2 = -9 * c ^ 4 - 6 + 304 * c := by
      linarith only [h]
    -- Show that 0 < r.
    have hc : 0 < r := by
      apply lt_of_le_of_ne hr
      by_contra! hr
      simp [h₄] at hr
      simp [hr] at h₀
      linarith only [show 0 < 2 * b ^ 2 + 3 by positivity, h₀]
    -- Show that 0 < c.
    simp [h₄] at hc
    -- Analyze the quadratic equation (2b + 3c²)² = -(9c⁴ + 6 - 304c).
    -- Since the left-hand side is non-negative, so is the right-hand.
    have h₅ : 9 * c ^ 4 ≤ 6 + 304 * c := by
      linarith only [h₀, sq_nonneg (2 * b + 3 * c ^ 2)]
    -- Show that c < 4.
    have h₆ : c < 4 := by
      contrapose! h₅
      rw [<-gt_iff_lt]
      -- If c ≥ 4, then 9 * 4 ^ 3 * c > 6 + 304 * c, contradiction.
      calc
        9 * c ^ 4 = 9 * c ^ 3 * c := by
          ring_nf
        _ ≥ 9 * 4 ^ 3 * c := by
          rw [ge_iff_le, mul_le_mul_right hc, mul_le_mul_left (by norm_num)]
          apply pow_le_pow_left₀ (by norm_num) h₅
        _ > 6 + 304 * c := by
          linarith only [show c ≥ 1 by omega]
    -- Analyze the cases of c : c = 1, 2 and 3,
    interval_cases c
    . -- Case c = 1.
      norm_num at h₀
      -- We have (2b+3)² = 289, hence 2b+3 = 17 or -17.
      rw [show (289 : ℤ) = 17 ^ 2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at h₀
      cases h₀ with
      | inl h₀ =>
        -- It corresponds to the solution (x, y) = (30, 21).
        rw [show b = 7 by linarith only [h₀]] at hb h₁
        rw [h₁] at ha
        tauto
      | inr h₀ =>
        -- It corresponds to the solution (x, y) = (-21, -30).
        rw [show b = -10 by linarith only [h₀]] at hb h₁
        rw [h₁] at ha
        tauto
    . -- Case c = 2.
      norm_num at h₀
      -- We have (2b+12)² = 458, which is not a perfect square, hence no solution.
      have h₇ : IsSquare (458 : ℤ) := by
        rw [<-h₀]
        simp [IsSquare]
        use (2 * b + 12)
        ring
      -- Assume on the contrary that t² = 458, then 21 < t < 22, no solution.
      simp [IsSquare] at h₇
      obtain ⟨t', h₇⟩ := h₇
      -- Let t = |t'| be the positive solution of t² = 458.
      let t := |t'|
      rw [<-pow_two, show t' ^ 2 = t ^ 2 by rw [sq_abs]] at h₇
      -- Now t is defined in such a way that 0 ≤ t.
      have ht : 0 ≤ t := by
        simp [t]
      linarith only [show 21 < t by nlinarith only [h₇, ht], show t < 22 by nlinarith only [h₇, ht]]
    . -- Case c = 3.
      norm_num at h₀
      -- We have (2b+27)² = 177, which is not a perfect square, hence no solution.
      have h₇ : IsSquare (177 : ℤ) := by
        rw [<-h₀]
        simp [IsSquare]
        use (2 * b + 27)
        ring
      -- Assume on the contrary that t² = 177, then 13 < t < 14, no solution.
      simp [IsSquare] at h₇
      obtain ⟨t', h₇⟩ := h₇
      -- Let t = |t'| be the positive solution of t² = 177.
      let t := |t'|
      rw [<-pow_two, show t' ^ 2 = t ^ 2 by rw [sq_abs]] at h₇
      -- Now t is defined in such a way that 0 ≤ t.
      have ht : 0 ≤ t := by
        simp [t]
      linarith only [show 13 < t by nlinarith only [h₇, ht], show t < 14 by nlinarith only [h₇, ht]]
  . -- The two solutions indeed satisfy the given equation.
    rintro (h | h)
    . -- If (x, y) = (30, 21), the equation is satisfied.
      simp [h]
      norm_num
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
    . -- If (x, y) = (-21, -30), the equation is satisfied.
      simp [h]
      norm_num
      rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      norm_num
