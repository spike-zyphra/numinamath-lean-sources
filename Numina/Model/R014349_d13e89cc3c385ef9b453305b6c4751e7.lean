import Mathlib

theorem algebra_269808 (f : ℝ → ℝ) (hf : f = fun x => (x ^ 2 - 1) / (x ^ 2 + 1)) :
    Set.range f = Set.Ico (-1) 1 := by 
  ext y
  simp [hf, Set.mem_range, Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · -- First, we'll prove that if $y \in \text{range } f$, then $y \in [-1, 1)$.
    rintro ⟨x, hx⟩
    have h1 : -1 ≤ y := by 
      have h2 : (x ^ 2 - 1 : ℝ) / (x ^ 2 + 1) ≥ -1 := by
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg x]
      linarith [hx, h2]
    
    have h2 : y < 1 := by
      have h3 : (x ^ 2 - 1 : ℝ) / (x ^ 2 + 1) < 1 := by
        apply (div_lt_iff₀ (by positivity)).mpr
        nlinarith [sq_nonneg x]
      linarith [hx, h3]
    
    constructor <;> linarith
  · -- Now prove the reverse: given $y \in [-1, 1)$, find $x$ such that $f(x) = y$.
    rintro ⟨hy1, hy2⟩
    
    have h3 : (1 + y) / (1 - y) ≥ 0 := by
      apply div_nonneg
      · -- Show 1 + y ≥ 0
        linarith
      · -- Show 1 - y ≥ 0
        linarith
    have h4 : ∃ s : ℝ, s ^ 2 = (1 + y) / (1 - y) := by
      use Real.sqrt ((1 + y) / (1 - y))
      rw [Real.sq_sqrt]
      linarith
    rcases h4 with ⟨s, hs⟩
    
    use s
    have h5 : (s ^ 2 - 1) / (s ^ 2 + 1) = y := by
      have h6 : s ^ 2 = (1 + y) / (1 - y) := hs
      have h7 : s ^ 2 + 1 > 0 := by
        have pos1 : (1 - y : ℝ) > 0 := by linarith
        nlinarith [show s ^ 2 ≥ 0 by nlinarith, h6, pos1]
      have h8 : s ^ 2 - 1 = y * (s ^ 2 + 1) := by
        rw [h6]
        field_simp [(show (1 - y : ℝ) ≠ 0 by linarith)]
        <;> nlinarith
      have pos1 : s ^ 2 + 1 > 0 := h7
      field_simp at h8 ⊢
      <;> nlinarith
      all_goals linarith
    linarith [h5]
  all_goals linarith