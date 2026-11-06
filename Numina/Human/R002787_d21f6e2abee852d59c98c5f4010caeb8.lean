import Mathlib

open Complex

-- Prove an auxiliary lemma:
-- |z| = |w| iff normSq z = normSq w.
lemma Complex.abs_eq_abs_iff_normSq_eq_normSq {z w : ℂ} : Complex.abs z = Complex.abs w ↔ Complex.normSq z = Complex.normSq w := by
  simp [Complex.abs]
  rw [Real.sqrt_inj (normSq_nonneg _) (normSq_nonneg _)]

-- Show that z ≠ w, |z| = |w|, |1 + z| = |1 + w| imply that z = w*.
lemma lemma_1 {z w : ℂ} (hz : Complex.abs z = Complex.abs w) (hw : z ≠ w)
    (hzw : Complex.abs (1 + z) = Complex.abs (1 + w)) : z = starRingEnd ℂ w := by
  rw [abs_eq_abs_iff_normSq_eq_normSq] at hz hzw
  -- We have z.re^2 + z.im^2 = w.re^2 + w.im^2 and
  -- (1 + z.re)^2 + z.im^2 = (1 + w.re)^2 + w.im^2.
  simp [normSq] at hz hzw
  -- We get z.re = w.re.
  have hre : z.re = w.re := by linarith
  rw [hre] at hz
  -- We also get z.im^2 = w.im^2.
  have him : z.im^2 = w.im^2 := by linarith
  apply Complex.ext
  · rw [conj_re, hre]
  -- It is left to show that z.im = -w.im.
  · rw [conj_im]
    -- z.im^2 = w.im^2 implies that z.im = w.im or z.im = -w.im.
    rw [sq_eq_sq_iff_abs_eq_abs, abs_eq_abs] at him
    cases' him with him him
    -- If z.im = w.im then we get z = w, a contradiction.
    · contrapose! hw
      apply Complex.ext hre him
    · exact him

-- Show that ‖z‖ = 1 implies that z / (z^2 + 1) = 1 / (2 * z.re).
lemma lemma_2 {z : ℂ} (hz : ‖z‖ = 1) : z / (z^2 + 1) = 1 / (2 * z.re) := by
  -- We have z* ≠ 0 (because ‖z*‖ = ‖z‖ > 0).
  have hz0 : starRingEnd ℂ z ≠ 0 := by
    rw [← normSq_pos, normSq_conj, normSq_eq_norm_sq, hz]
    norm_num
  -- We have z / (z^2 + 1) = (z * z*) / ((z^2 + 1) * z*) = ‖z‖^2 / (z * ‖z‖^2 + z*)
  --         = 1 / (z + z*) = 1 / (2 * z.re).
  rw [← mul_div_mul_right _ _ hz0]
  rw [add_mul, show ∀ x, z^2 * x = z * (z * x) by intros; ring]
  simp [mul_conj, normSq_eq_norm_sq, hz, add_conj]

-- Show that {z / (z^2 + 1) | z ∈ ℂ \ ℝ, z ≠ ±I} = (-∞, -1/2) ∪ (1/2, ∞).
lemma lemma_3 : {w : ℂ | ∃ z : ℂ, w = z / (z^2 + 1) ∧ ‖z‖ = 1 ∧ z ≠ I ∧ z ≠ -I ∧ ∀ r : ℝ, z ≠ r}
    = ofReal '' (Set.Iio (-1 / 2 : ℝ) ∪ Set.Ioi (1 / 2)) := by
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  constructor
  · intro ⟨z, hw, hz, hz1, hz2, hr⟩
    -- Assume that w = z / (z^2 + 1), ‖z‖ = 1, z ≠ ±I, and z ≠ r for all r ∈ ℝ.
    -- Show that there exists x such that x = w and x < -1/2 or 1/2 < x.
    -- lemma_2 implies that w = 1 / (2 * z.re).
    rw [lemma_2 hz] at hw
    -- Take x = 1 / (2 * z.re).
    use 1 / (2 * z.re)
    simp [hw]
    -- Show that |z.re| ≤ 1 nad z.re ≠ 0.
    have ⟨hre1, hre0⟩ : |z.re| ≤ 1 ∧ z.re ≠ 0 := by
      -- ‖z‖ = 1 implies that z.re^2 + z.im^2 = 1, so |z.re| ≤ 1.
      simp [Complex.abs, normSq] at hz
      constructor
      · rw [abs_le]
        constructor <;> nlinarith
      have hzi : z ≠ I ∧ z ≠ -I := ⟨hz1, hz2⟩
      -- Suppose that z.re = 0 and show that z = I or z = -I.
      contrapose! hzi
      intro h
      simp [hzi, ← pow_two] at hz
      cases' hz with hz hz
      · contrapose! h
        apply Complex.ext <;> simp [hzi, hz]
      · apply Complex.ext <;> simp [hzi, hz]
    -- Show that |z.re| < 1.
    have hre : |z.re| < 1 := by
      -- It is enough to show taht |z.re| ≠ 1.
      simp [lt_iff_le_and_ne, hre1]
      -- Assume that |z.re| = 1 and show that z = r for some r ∈ ℝ.
      contrapose! hr
      use z.re
      simp [Complex.abs, normSq] at hz
      -- If z.re = 1 then z.im = 0 and so z = z.re.
      rw [show z.re * z.re = |z.re|^2 by simp [pow_two], hr] at hz
      have him : z.im = 0 := by nlinarith
      apply Complex.ext <;> simp [him]
    rw [abs_lt] at hre
    -- Consider two cases: z.re < 0 and 0 ≤ z.re.
    by_cases h0 : z.re < 0
    · left
      -- If z.re < 0 then show that 1 / (2 * z.re) < -1/2.
      rw [show (-1 / 2 : ℝ) = -1 * 2⁻¹ by norm_num]
      gcongr
      -- It is enough to show that 1 / z.re < -1 which is equivalent to
      -- 1 < 1 / -z.re.
      suffices 1 < (-z.re)⁻¹ by
        simp [inv_neg] at this
        linarith
      -- It is enough to show that -z.re < 1 or -1 < z.re.
      rw [one_lt_inv₀ (by linarith)]
      linarith
    · right
      -- If 0 ≤ z.re then 0 < z.re (from z.re ≠ 0).
      -- To show that 1 / (2 * z.re) < 1 / 2 it is enough to show that 0 < z.re < 1.
      simp [one_lt_inv_iff₀, hre]
      simp at h0
      simp [lt_iff_le_and_ne, h0, hre0.symm]
  · intro ⟨x, h, hxw⟩
    -- Assume that x < -1/2 or 1/2 < x and z / (z^2 + 1) = x.
    -- Show that ‖z‖ = 1, z ≠ ±I, and z ≠ r for all r ∈ ℝ.
    have hx0 : x ≠ 0 := by cases h <;> linarith
    -- Define a = 1 / (2 * x), b = √(1 - a^2), z = a + b * I.
    set a := 1 / (2 * x)
    set b := √(1 - a^2)
    set z := a + b * I
    have ⟨hz_re, hz_im⟩ : z.re = a ∧ z.im = b := by simp [z]
    -- We have a ≠ 0 (because x ≠ 0).
    have ha0 : a ≠ 0 := by simp [a, hx0]
    -- Show that |a| < 1.
    have ha1 : |a| < 1 := by
      simp only [a, abs_div, abs_one, abs_mul, _root_.abs_two]
      rw [div_lt_one (by positivity)]
      -- It is enough to show that 1 / 2 < |x|.
      suffices 1 / 2 < |x| by linarith
      rw [lt_abs, lt_neg, ← neg_div]
      exact h.symm
    -- Show that 0 < b.
    have hb0 : 0 < b := by simp [b, ha1]
    -- Show that b < 1.
    have hb1 : b < 1 := by
      -- The result follows from a ≠ 0 and |a| < 1.
      simp [b]
      rw [show 1 = √1 by simp]
      apply Real.sqrt_lt_sqrt
      · simp [le_of_lt ha1]
      · simp
        positivity
    -- a^2 + b^2 = 1 so ‖z‖ = 1.
    have hz : ‖z‖ = 1 := by
      simp [Complex.abs, normSq, hz_re, hz_im, ← pow_two, b]
      rw [Real.sq_sqrt (by simp [le_of_lt ha1])]
      ring
    use z
    rw [lemma_2 hz, hz, hz_re, ← hxw]
    constructorm* _ ∧ _
    · simp [a]; ring
    · rfl
    · -- Show that z ≠ I.
      -- Assume that z = I and show that 1 ≤ b.
      contrapose! hb1
      apply_fun im at hb1
      simp [hz_im] at hb1
      linarith
    · -- Show that z ≠ -I.
      -- Assume that z = -I and show that b ≤ 0.
      contrapose! hb0
      apply_fun im at hb0
      simp [hz_im] at hb0
      linarith
    · -- Show that z ≠ r for all r ∈ ℝ.
      intro r
      -- Assume that z = r and show that b ≤ 0.
      contrapose! hb0
      apply_fun im at hb0
      simp [hz_im] at hb0
      rw [hb0]

/- Subject (2).

a) Let $z$ and $w$ be two distinct complex numbers such that $|z|=|w|$ and $|1+z|=|1+w|$. Show that $z=\bar{w}$.

b) Show that if $z \neq \pm i$ is a complex number of modulus 1, then $x=\frac{z}{z^{2}+1}$ is a real number.

Determine the set $\left\{\left.\frac{z}{z^{2}+1}|z \in \mathbb{C} \backslash \mathbb{R}, z \neq \pm i| z \right\rvert\,,=1\right\}$.

Supplements from G.M.-B. no. 4/2014 and 11/2014 -/
theorem algebra_112983 :
    (∀ z w : ℂ, Complex.abs z = Complex.abs w → z ≠ w →
       Complex.abs (1 + z) = Complex.abs (1 + w) → z = starRingEnd ℂ w) ∧
    (∀ z : ℂ, ‖z‖ = 1 → z ≠ I ∧ z ≠ -I → ∃ x : ℝ, z / (z^2 + 1) = x) ∧
    ({w : ℂ | ∃ z : ℂ, w = z / (z^2 + 1) ∧ ‖z‖ = 1 ∧ z ≠ I ∧ z ≠ -I ∧ ∀ r : ℝ, z ≠ r} = ofReal '' (Set.Iio (-1 / 2 : ℝ) ∪ Set.Ioi (1 / 2))) := by
  constructorm* _ ∧ _
  · apply lemma_1
  · intro z hz hzi
    use 1 / (2 * z.re)
    simp [lemma_2 hz]
  · apply lemma_3