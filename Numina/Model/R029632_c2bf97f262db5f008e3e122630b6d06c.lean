import Mathlib

theorem number_theory_231735 (x : ℝ) (hx : x > 0) (h : ∃ r, Int.fract x = r * x ∧ x = r * Int.floor x) :
    Int.fract x = (Real.sqrt 5 - 1) / 2 := by 
  rcases h with ⟨r, h1, h2⟩
  have h3 : Int.fract x = x - (↑(Int.floor x) : ℝ) := by 
    rw [Int.fract]
    <;> simp
    <;> linarith
  rw [h3] at h1 
  by_cases h4 : Int.floor x = 0 
  · -- If Int.floor x = 0, then x < 1 
    have h7 : (↑(Int.floor x) : ℝ) = (0 : ℝ) := by 
      rw [h4]
      all_goals norm_num 
    rw [h7] at h1 h2 
    -- So h1: x = r*x => r=1 (because x ≠0)
    -- h2: x =0 contradicts x >0
    -- This can't happen. An inconsistency would be raised by Lean.
    nlinarith 
  · -- Int.floor x ≠0 
    have h8 : (↑(Int.floor x) : ℝ) ≠ 0 := by 
      by_contra h9
      have h10 : (Int.floor x : Int) = 0 := by 
        have h11 : (↑(Int.floor x) : ℝ) = (0 : ℝ) := by nlinarith 
        have h12 : (Int.floor x : Int) = 0 := by 
          exact_mod_cast (show (Int.floor x : ℝ) = (0 : ℝ) from by linarith)
        exact_mod_cast h12 
      tauto 
    have h9 : ↑(Int.floor x) = x * (1 - r) := by 
      have h10 : x - ↑(Int.floor x) = r * x := by linarith 
      nlinarith 
    have h10 : x = r * (↑(Int.floor x) ) := by 
      linarith 
    rw [show ↑(Int.floor x) = x * (1 - r) by linarith [h9]] at h10 
    have h11 : r^2 - r + 1 = 0 := by 
      have h12 : x > 0 := hx 
      have h13 : r * (1 - r) = 1 := by 
        nlinarith 
      nlinarith 
    have h14 : r^2 - r + 1 > 0 := by 
      nlinarith [sq_nonneg (r - 1 / 2)]
    nlinarith