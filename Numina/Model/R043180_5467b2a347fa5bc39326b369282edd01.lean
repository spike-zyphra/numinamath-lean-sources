import Mathlib
theorem algebra_184863 {f : ℝ → ℝ} (hf : ∀ x, x ≥ 0 → f x = |x - 2| + a) (ha : ∀ x, f (-x) = -f x) :
{x | f x ≥ 1} = {x | x ∈ Set.Icc (-3) (-1) ∨ x ∈ Set.Ici 5}:= by
  have ha2 : a = -2 := by 
    have h1 := ha 0
    have h2 := hf 0 (show (0 : ℝ) ≥ 0 by norm_num)
    norm_num at h2 
    have eq1 : f 0 = 0 := by 
      specialize ha 0 
      norm_num at ha 
      linarith 
    linarith [eq1, h2]

  have hfx1 : ∀ x, x ≥ 0 → f x = |x - 2| - 2 := by 
    intro x hx 
    have hx1 := hf x hx 
    rw [ha2] at hx1 
    linarith

  have hfx2 : ∀ x, x < 0 → f x = -|-x - 2| + 2 := by
    intro x hx 
    have h1 := ha x 
    have h2 : -x ≥ 0 := by linarith 
    have hfx3 : f (-x) = |(-x) - 2| - 2 := by 
      apply hfx1 
      linarith 
    rw [hfx3] at h1 
    have eq1 : f x = -(|(-x) - 2| - 2) := by 
      linarith [h1]
    have eq2 : f x = -|-x - 2| + 2 := by 
      have h3 : |(-x) - 2| = |(-x - 2)| := by 
        ring_nf 
      rw [h3] at eq1 
      have h4 : |-x - 2| = |(-x - 2)| := by 
        ring_nf 
      rw [h4] at * 
      linarith 
    linarith [eq2]

  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Icc, Set.mem_Ici]
  by_cases h : x ≥ 0 
  · -- x ≥ 0
    have hfx : f x = |x - 2| - 2 := hfx1 x h 
    rw [hfx] 
    constructor 
    · -- Assume |x - 2| - 2 ≥ 1 
      intro h1 
      have h2 : |x - 2| ≥ 3 := by linarith 
      cases' abs_choice (x - 2) with h3 h3 
      · -- x - 2 ≥ 0 
        right 
        have h4 : x ≥ 5 := by linarith 
        simpa using h4 
      · -- x - 2 < 0 
        exfalso 
        linarith 
    · -- Assume x ∈ Set.Icc (-3) (-1) ∨ x ∈ Set.Ici 5
      rintro (h1 | h2)
      · -- x ∈ Set.Icc (-3) (-1)
        exfalso 
        linarith 
      · -- x ∈ Set.Ici 5 
        have h3 : x ≥ 5 := by 
          simpa using h2 
        have h4 : |x - 2| ≥ 3 := by 
          have h5 : x - 2 ≥ 3 := by linarith 
          rw [abs_of_nonneg (by linarith)]
          linarith 
        linarith [abs_of_nonneg (by linarith : x - 2 ≥ 0), h4]
  · -- x < 0 
    have hfx : f x = -|-x - 2| + 2 := hfx2 x (by linarith) 
    rw [hfx] 
    constructor 
    · -- Assume -|-x - 2| + 2 ≥ 1 
      intro h1 
      have h6 : |-x - 2| ≤ 1 := by linarith 
      have h7 : -1 ≤ (-x - 2) := by 
        cases' abs_le.mp h6 with h8 h9 
        linarith 
      have h8 : (-x - 2) ≤ 1 := by 
        cases' abs_le.mp h6 with h8 h9 
        linarith 
      have h9 : x ≤ -1 := by 
        linarith 
      have h10 : x ≥ -3 := by 
        linarith 
      left 
      constructor
      · -- Show that -3 ≤ x 
        linarith 
      · -- Show that x ≤ -1 
        linarith 
    · -- Assume x ∈ Set.Icc (-3) (-1) ∨ x ∈ Set.Ici 5 
      rintro (h1 | h2)
      · -- x ∈ Set.Icc (-3) (-1)
        have h3 : -3 ≤ x := by 
          linarith [h1.1] 
        have h4 : x ≤ -1 := by 
          linarith [h1.2] 
        have h5 : |-x - 2| ≤ 1 := by 
          have h6 : -x - 2 ≤ 1 := by 
            nlinarith 
          have h7 : -1 ≤ -x - 2 := by 
            nlinarith 
          apply abs_le.mpr 
          constructor <;> linarith 
        linarith [abs_le.mp h5] 
      · -- x ∈ Set.Ici 5 
        exfalso 
        linarith