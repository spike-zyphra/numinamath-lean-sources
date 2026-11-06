import Mathlib

theorem algebra_9563 :
    IsLeast {x : ℕ | x ∈ Finset.Icc 100 999 ∧ x = (x : ℝ).sqrt + 930} 961 := by
  constructor
  · -- Show 961 is in the set
    constructor
    · -- Show 961 is in the range [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show 961 satisfies the equation
      have h1 : ((961 : ℝ) : ℝ) = (961 : ℝ).sqrt + 930 := by
        have h2 : (961 : ℝ).sqrt = 31 := by
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
        rw [h2]
        all_goals norm_num
      exact_mod_cast h1
  · -- Show that 961 is the minimum
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    rw [Finset.mem_Icc] at hx1
    rcases hx1 with ⟨hx1l, hx1u⟩
    by_contra h
    push_neg at h
    have h3 : x ≤ 960 := by
      omega
    have h4 : (x : ℝ) ≥ (100 : ℝ) := by
      exact_mod_cast (show x ≥ 100 by omega)
    have h5 : (x : ℝ) ≤ (999 : ℝ) := by
      exact_mod_cast (show x ≤ 999 by omega)
    have h6 : (x : ℝ) = (x : ℝ).sqrt + (930 : ℝ) := by
      exact_mod_cast hx2
    have h7 : (x : ℝ).sqrt ≥ 0 := by
      apply Real.sqrt_nonneg
    have h8 : ((x : ℝ).sqrt) ^ 2 = (x : ℝ) := by
      rw [Real.sq_sqrt]
      have h9 : (x : ℝ) ≥ 0 := by
        exact_mod_cast (show x ≥ 0 by omega)
      linarith
    have h9 : ((x : ℝ).sqrt) ^ 2 - (x : ℝ).sqrt - 930 = 0 := by
      nlinarith [h6, h8]
    have h10 : (x : ℝ).sqrt - 31 = 0 := by
      have h11 : ((x : ℝ).sqrt - 31) * ((x : ℝ).sqrt + 30) = 0 := by
        nlinarith [h9]
      cases' (mul_eq_zero.1 h11) with h12 h13
      · -- Case where sqrt(x) - 31 = 0
        linarith
      · -- Case where sqrt(x) + 30 = 0
        nlinarith [Real.sqrt_nonneg (x : ℝ)]
    have h11 : (x : ℝ).sqrt = 31 := by
      linarith
    have h12 : (x : ℝ) = 961 := by
      calc
        (x : ℝ) = ((x : ℝ).sqrt) ^ 2 := by
          rw [Real.sq_sqrt]
          have h9 : (x : ℝ) ≥ 0 := by
            exact_mod_cast (show x ≥ 0 by omega)
          linarith
        _ = (31 : ℝ) ^ 2 := by
          rw [h11]
        _ = (961 : ℝ) := by
          norm_num
    have h13 : x = 961 := by
      exact_mod_cast (show (x : ℝ) = (961 : ℝ) by linarith)
    omega