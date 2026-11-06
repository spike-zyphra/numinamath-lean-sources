import Mathlib

theorem inequalities_306274 (a b c : ℝ) (h₀ : a ≠ b) (h₁ : b ≠ c) (h₂ : c ≠ a) :
    3 / 2 ≤ (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) / (|a - b| + |b - c| + |c - a|) ∧
    (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) / (|a - b| + |b - c| + |c - a|) < 2 := by
  have h3 : 0 < |a - b| := by 
    apply abs_pos.mpr
    intro h
    apply h₀
    linarith
  -- prove the positivity of |b - c| and |c - a|
  have h4 : 0 < |b - c| := by
    apply abs_pos.mpr
    intro h
    apply h₁
    linarith
  have h5 : 0 < |c - a| := by
    apply abs_pos.mpr
    intro h
    apply h₂
    linarith
  have h6 : 0 < |a - b| + |b - c| + |c - a| := by 
    positivity
  constructor
  · -- Prove the lower bound
    have h7 : (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) ≥ 3 / 2 * (|a - b| + |b - c| + |c - a|) := by
      cases' abs_cases (a + b - 2 * c) with h11 h11 <;> 
      cases' abs_cases (b + c - 2 * a) with h12 h12 <;> 
      cases' abs_cases (c + a - 2 * b) with h13 h13 <;> 
      cases' abs_cases (a - b) with h14 h14 <;> 
      cases' abs_cases (b - c) with h15 h15 <;> 
      cases' abs_cases (c - a) with h16 h16 <;> 
      all_goals
        linarith
    have h7 : (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) / (|a - b| + |b - c| + |c - a|) ≥ 3 / 2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      linarith
    linarith
  · -- Prove the upper bound
    have h8 : (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) < 2 * (|a - b| + |b - c| + |c - a|) := by
      cases' abs_cases (a + b - 2 * c) with h11 h11 <;> 
      cases' abs_cases (b + c - 2 * a) with h12 h12 <;> 
      cases' abs_cases (c + a - 2 * b) with h13 h13 <;> 
      cases' abs_cases (a - b) with h14 h14 <;> 
      cases' abs_cases (b - c) with h15 h15 <;> 
      cases' abs_cases (c - a) with h16 h16 <;> 
      all_goals
        linarith
    have h9 : (|a + b - 2 * c| + |b + c - 2 * a| + |c + a - 2 * b|) / (|a - b| + |b - c| + |c - a|) < 2 := by
      apply (div_lt_iff₀ (by positivity)).mpr
      linarith
    linarith