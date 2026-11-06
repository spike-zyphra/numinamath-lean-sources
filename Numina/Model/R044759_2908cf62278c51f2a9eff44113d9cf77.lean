import Mathlib

theorem algebra_11513 (a b : ℝ) (ha : a < 0) (f : ℝ → ℝ)
    (hf : ∀ x ∈ Set.Icc 0 1, f x = a * x + b) :
    Set.image f (Set.Icc 0 1) = Set.Icc (a + b) b := by
  ext y 
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · -- First, prove that if y is in the image, then it's in the interval
    rintro ⟨x, hx, hfx⟩
    rcases hx with ⟨hx0, hx1⟩
    rw [hf x ⟨by linarith, by linarith⟩] at hfx
    constructor 
    · -- Show that y ≥ a + b
      nlinarith 
    · -- Show that y ≤ b
      nlinarith 
  · -- Now prove the reverse: if y is in the interval [a + b, b], then it's in the image
    rintro ⟨hy1, hy2⟩
    have h1 : a < 0 := ha
    use ( (y - b) / a )
    constructor
    · -- Show that x ∈ [0, 1]
      constructor 
      · -- Show 0 ≤ (y - b) / a 
        have h3 : (y - b) / a ≥ 0 := by
          apply (le_div_iff_of_neg' (by linarith)).mpr 
          linarith 
        linarith 
      · -- Show (y - b) / a ≤ 1 
        have h4 : (y - b) / a ≤ 1 := by 
          apply (div_le_iff_of_neg' (by linarith)).mpr 
          linarith 
        linarith 
    · -- Show that f((y - b) / a) = y 
      have hfx : f ( (y - b) / a ) = a * ( (y - b) / a ) + b := by 
        apply hf 
        constructor 
        · -- Show 0 ≤ (y - b) / a 
          have h3 : (y - b) / a ≥ 0 := by
            apply (le_div_iff_of_neg' (by linarith)).mpr 
            linarith 
          linarith 
        · -- Show (y - b) / a ≤ 1 
          have h4 : (y - b) / a ≤ 1 := by 
            apply (div_le_iff_of_neg' (by linarith)).mpr 
            linarith 
          linarith 
      rw [hfx]
      field_simp [(show a ≠ 0 by linarith)]
      <;> linarith