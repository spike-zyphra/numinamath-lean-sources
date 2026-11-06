import Mathlib

open Real Set
open scoped Real

/- Solve
\[\arcsin (\sin x) = \frac{x}{2}.\]Enter all the solutions, separated by commas. -/
theorem calculus_17155 :
    {x : ℝ | arcsin (sin x) = x / 2} = {-2 * π / 3, 0, 2 * π / 3} := by
    apply Set.ext
    simp
    intro x
    constructor
    intro hx
    -- Since $\frac{x}{2} = \arcsin (\sin x),$ we must have $-\frac{\pi}{2} \le \frac{x}{2} \le \frac{\pi}{2},$ or [-\pi \le x \le \pi.]
    have h1 := Real.arcsin_mem_Icc (sin x)
    simp [hx] at h1
    -- Taking the sine of both sides of the given equation, we get [\sin (\arcsin (\sin x)) = \sin \frac{x}{2},]which simplifies to [\sin x = \sin \frac{x}{2}.]
    have h2 : sin x = sin (x / 2) := by 
      have : sin x = sin (arcsin (sin x)) := by 
        have : sin x ≤ 1 := sin_le_one x
        have this' : - 1 ≤ sin x := neg_one_le_sin x
        rw [Real.sin_arcsin this' this]
      rw [this,hx]
    -- Then from the double angle formula, [2 \sin \frac{x}{2} \cos \frac{x}{2} = \sin \frac{x}{2},]
    have h3 : 2 * sin (x / 2) * cos (x / 2) = sin (x / 2) := by
      nth_rewrite 2 [← h2]
      have : x = x / 2 * 2 := by ring_nf
      nth_rewrite 3 [this]
      rw [mul_two,sin_add,mul_assoc,two_mul] ;ring
    -- so $2 \sin \frac{x}{2} \cos \frac{x}{2} - \sin \frac{x}{2} = 0.$ This factors as [\sin \frac{x}{2} \left( 2 \cos \frac{x}{2} - 1 \right) = 0,]so $\sin \frac{x}{2} = 0$ or $\cos \frac{x}{2} = \frac{1}{2}.$
    have h4 : 2 * sin (x / 2) * (cos (x / 2) - 1 / 2) = 0 := by linarith
    simp at h4
    -- If $\sin \frac{x}{2} = 0,$ then $x = 0.$ 
    rcases h4 with h4|h4
    · have : x / 2 = 0 := by
        have : π / 2 < π := by
          norm_num ;exact pi_pos
        apply (Real.sin_eq_zero_iff_of_lt_of_lt ?_ ?_).mp h4
        linarith ;linarith
      simp at this
      simp [this]
    --  If $\cos \frac{x}{2} = \frac{1}{2},$ then $x = \pm \frac{2 \pi}{3}.$ 
    have h5 : cos (π / 3) = 2⁻¹ := by
      norm_num
    rw [← h5] at h4
    have h6 : x / 2 = π / 3 ∨ x / 2 = -(π / 3) := by
      have : cos (x / 2) = cos (π / 3) := by linarith
      apply Real.cos_eq_cos_iff.mp at this
      rcases this with ⟨k,hk|hk⟩
      <;> have hk' : π / 3 - π / 2 ≤ 2 * k * π := by linarith  
      · have hk'' : 2 * k * π ≤ π / 3 + π / 2:= by linarith
        have : k = 0 := by
          by_cases hk1 : 1 ≤ k
          have hk1' : (1:ℝ) ≤ k := Int.cast_one_le_of_pos hk1
          have : 2 * π ≤ π / 3 + π / 2 := by nlinarith
          linarith [pi_pos]
          by_cases hk2 : k ≤ -1
          have hk2' : k ≤ ((-1:ℤ):ℝ) := Int.cast_le.mpr hk2
          simp at hk2'
          have :   π / 3 - π / 2 ≤ -2 * π := by nlinarith
          linarith [pi_pos]
          interval_cases k
          rfl
        simp [this] at hk
        simp [hk]
      have hk'' : 2 * k * π ≤ π / 3 + π / 2:= by linarith
      have : k = 0 := by
          by_cases hk1 : 1 ≤ k
          have hk1' : (1:ℝ) ≤ k := Int.cast_one_le_of_pos hk1
          have : 2 * π ≤ π / 3 + π / 2 := by nlinarith
          linarith [pi_pos]
          by_cases hk2 : k ≤ -1
          have hk2' : k ≤ ((-1:ℤ):ℝ) := Int.cast_le.mpr hk2
          simp at hk2'
          have :   π / 3 - π / 2 ≤ -2 * π := by nlinarith
          linarith [pi_pos]
          interval_cases k
          rfl
      simp [this] at hk
      simp [hk]
    have : x = x / 2 * 2 := by ring
    rw [this]
    rcases h6 with h6|h6
    · simp [h6] ;ring_nf ;simp
    simp [h6] ;ring_nf ;simp
    --  We check that all these values work, so the solutions are these
    intro hx
    rcases hx with hx|hx|hx
    · rw[hx,neg_div,sin_neg,arcsin_neg]
      have : sin (2 * π / 3) = sin (π / 3) := by 
        apply sin_eq_sin_iff.mpr
        use 0
        right
        simp ;ring
      rw [this,arcsin_sin]
      ring_nf
      linarith [pi_pos]
      linarith [pi_pos]
    · rw [hx] ;simp
    · have : sin (2 * π / 3) = sin (π / 3) := by 
        apply sin_eq_sin_iff.mpr
        use 0
        right
        simp ;ring
      rw [hx,this,arcsin_sin] ;ring
      linarith [pi_pos]
      linarith [pi_pos]

            