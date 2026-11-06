import Mathlib

open Real

/- Let $t$ be the smallest positive real number for which $\cos t = \cos t^\circ.$  (We are taking the cosine of $t$ radians on the left and of $t$ degrees on the right.)  Determine $\lfloor t \rfloor.$-/
theorem calculus_23362 {t : ℝ} (ht : IsLeast {x | 0 < x ∧ Real.cos x = Real.cos (x * π / 180)} t) :
    ⌊t⌋ = 6 := by
  rcases ht with ⟨⟨htpos, hteq⟩, ht⟩
  simp [lowerBounds] at ht
  --   If the cosines of two angles (in degrees) are equal,
  -- either their difference is a multiple of $360^\circ,$
  -- or their sum is a multiple of $360^\circ.$
  -- Thus, $t + \frac{180t}{\pi} = 360^\circ k$ for $t - \frac{180t}{\pi} = 360^\circ k.$
  rw [Real.cos_eq_cos_iff] at hteq
  rcases hteq with ⟨k, hk⟩
  -- We need the following condition to perform `field_simp`.
  have h1 : π / 180 - 1 < 0 := by
    suffices π < 180 by linarith
    apply lt_trans pi_lt_315
    norm_num
  have h2 : π - 180 < 0 := by
    suffices π < 180 by linarith
    apply lt_trans pi_lt_315
    norm_num
  have h3 : 0 < π / 180 + 1 := by positivity
  -- From the first equation,
  -- \[t = \frac{360^\circ \pi k}{\pi + 180}.\]
  -- From the second equation,
  -- \[t = \frac{360^\circ \pi k}{\pi - 180}.\]
  replace hk : t = (π / 180 - 1)⁻¹ * 2 * k * π ∨
      t = (π / 180 + 1)⁻¹ * 2 * k * π := by
    refine Or.imp (fun h => ?_) (fun h => ?_) hk
    . have := h2.ne
      field_simp at h ⊢
      linear_combination h
    field_simp at h ⊢
    linear_combination h
  have : 0 < -(π / 180 - 1)⁻¹ := by
    suffices (π / 180 - 1)⁻¹ < 0 by linarith
    rwa [inv_lt_zero]
  -- The smallest positive real number of this form is $\frac{360 \pi}{\pi + 180}.$
  -- The smallest positive real number of this form is $\frac{360 \pi}{180 - \pi}.$
  have h : t = (π / 180 - 1)⁻¹ * 2 * (-1) * π ∨
      t = (π / 180 + 1)⁻¹ * 2 * 1 * π := by
    refine Or.imp (fun h => ?_) (fun h => ?_) hk
    . rcases lt_trichotomy k (-1) with hk1 | hk1 | hk1
      swap
      . rw [hk1] at h
        convert h
        norm_num
      . contrapose! ht
        set a : ℝ := (π / 180 - 1)⁻¹ * 2 * (-1) * π with ha
        use a
        constructor
        . suffices 0 < (-(π / 180 - 1)⁻¹) * 2 * π by linarith
          positivity
        constructor
        . rw [Real.cos_eq_cos_iff]
          use -1
          left
          have := h2.ne
          field_simp at ha ⊢
          linear_combination ha
        rw [ha, h]
        gcongr ?_ * π
        conv => congr; rw [mul_right_comm]; rfl; rw [mul_right_comm]
        gcongr ?_ * 2
        suffices (-(π / 180 - 1)⁻¹) * 1 < (-(π / 180 - 1)⁻¹) * (-k) by
          convert this using 1
          . ring
          . ring
        gcongr
        norm_cast
        omega
      if hk0 : k = 0 then
        rw [hk0] at h
        norm_num [h] at htpos
      else
        suffices t < 0 by linarith
        rw [h]
        suffices 0 < (-(π / 180 - 1)⁻¹) * 2 * k * π by linarith
        have : 0 < k := by omega
        positivity
    rcases lt_trichotomy k 1 with hk1 | hk1 | hk1
    swap
    . rw [hk1] at h
      convert h
      norm_num
    . if hk0 : k = 0 then
        norm_num [hk0] at h
        norm_num [h] at htpos
      else
        have : 0 < -k := by omega
        have : 0 < -(k : ℝ) := by assumption_mod_cast
        have : 0 < (π / 180 + 1)⁻¹ := by positivity
        have : t < 0 := by
          rw [h]
          suffices 0 < (π / 180 + 1)⁻¹ * 2 * (-k) * π by linarith
          positivity
        linarith
    contrapose! ht
    set a : ℝ := (π / 180 + 1)⁻¹ * 2 * 1 * π with ha
    use a
    constructor
    . positivity
    constructor
    . rw [Real.cos_eq_cos_iff]
      use 1
      right
      field_simp at ha ⊢
      linear_combination ha
    rw [ha, h]
    gcongr ?_ * π
    gcongr (π / 180 + 1)⁻¹ * ?_
    norm_cast
  --Therefore, $t = \frac{360 \pi}{\pi + 180} \approx 6.175,$ so $\lfloor t \rfloor = \boxed{6}.$
  rcases h with h | h
  . contrapose! ht
    set a : ℝ := (π / 180 + 1)⁻¹ * 2 * 1 * π with ha
    use a
    constructor
    . positivity
    constructor
    . rw [Real.cos_eq_cos_iff]
      use 1
      right
      have := h2.ne
      field_simp at ha ⊢
      linear_combination ha
    rw [ha, h]
    field_simp
    rw [div_lt_iff (by positivity)]
    suffices 180 * 2 * π * 1 < 180 * 2 * π * ((π + 180) / (180 - π)) by
      convert this using 1
      . ring
      have := h2.ne
      have : 180 - π ≠ 0 := fun h => by rw [sub_eq_zero] at h; norm_num [← h] at this
      field_simp
      ring
    gcongr
    rw [lt_div_iff]
    linarith [pi_pos]
    . suffices π < 180 by linarith
      apply lt_trans pi_lt_315
      norm_num
  rw [h]
  field_simp
  rw [Int.floor_eq_iff]
  constructor
  . push_cast
    rw [le_div_iff₀ (by positivity)]
    suffices 6 * 180 ≤ 354 * π by linarith
    rw [← div_le_iff₀' (by positivity)]
    refine le_trans ?_ pi_gt_314.le
    norm_num
  rw [div_lt_iff (by positivity)]
  suffices 353 * π < 7 * 180 by push_cast; linarith
  rw [← lt_div_iff' (by norm_num)]
  apply lt_trans pi_lt_315
  norm_num
