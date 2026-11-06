import Mathlib

theorem algebra_308321 (a b c k : ℝ) (ha : a ≠ 0) (h1 : 4 = a + b + c) (h2 : 7 = 4*a + 2*b + c)
    (hk : k = -b/(2*a)) (habs : |k| ≤ 1) :
    3/5 ≤ a ∧ a ≤ 3 := by
  have eq1 : b = 3 - 3 * a := by
    have eq2 : c = 4 - a - b := by 
      linarith 
    rw [eq2] at h2
    linarith 
  have hk1 : -1 ≤ k := by
    cases' abs_le.mp habs with h1 h2
    linarith 
  have hk2 : k ≤ 1 := by
    cases' abs_le.mp habs with h1 h2
    linarith 
  have h4 : -1 ≤ -b / (2 * a) := by
    have : k = -b / (2 * a) := by 
      exact_mod_cast hk 
    linarith [show -1 ≤ k from hk1, this]
  have h3 : -b / (2 * a) ≤ 1 := by
    have : k = -b / (2 * a) := by 
      exact_mod_cast hk 
    linarith [show k ≤ 1 from hk2, this]
  -- Prove 3/5 ≤ a
  have h5 : 3/5 ≤ a := by
    have eq1' : b = 3 - 3 * a := eq1
    have h4' : -1 ≤ -b / (2 * a) := h4
    have h4'' : -1 ≤ -(3 - 3 * a) / (2 * a) := by 
      rw [eq1] at h4 
      linarith 
    by_cases h9 : a > 0
    · -- If a > 0
      have h11 : -1 ≤ -(3 - 3 * a) / (2 * a) := h4''
      have h12 : -1 * (2 * a) ≤ - (3 - 3 * a) := by
        apply (le_div_iff₀ (by linarith)).mp at h11
        linarith 
      nlinarith 
    · -- If a ≤ 0, so a < 0.
      have h6 : a < 0 := by 
        by_contra h7
        push_neg at h7 
        have : a = 0 := by linarith 
        contradiction 
      have h7 : - (3 - 3 * a) / (2 * a) ≤ 1 := by
        rw [eq1] at h3 
        linarith 
      have h13 : -1 * (2 * a) ≥ - (3 - 3 * a) := by
        have h4' : -1 ≤ -(3 - 3 * a) / (2 * a) := h4''
        apply (le_div_iff_of_neg' (by linarith)).mp at h4'
        linarith 
      have h14 : - (3 - 3 * a) ≥ 2 * a := by 
        have h7' : - (3 - 3 * a) / (2 * a) ≤ 1 := h7 
        apply (div_le_iff_of_neg' (by linarith)).mp at h7' 
        linarith 
      nlinarith 
  -- Prove a ≤ 3
  have h6 : a ≤ 3 := by
    have eq1' : b = 3 - 3 * a := eq1
    have h3 : -b / (2 * a) ≤ 1 := by
      have : k = -b / (2 * a) := by 
        exact_mod_cast hk 
      linarith [show k ≤ 1 from hk2, this]
    have h7 : - (3 - 3 * a) / (2 * a) ≤ 1 := by 
      rw [eq1] at h3 
      linarith 
    by_cases h9 : a > 0 
    · -- If a > 0
      have h8' : - (3 - 3 * a) ≤ 2 * a := by
        have h7' : - (3 - 3 * a) / (2 * a) ≤ 1 := h7
        apply (div_le_iff₀ (by linarith)).mp at h7'
        linarith 
      nlinarith 
    · -- Assume a ≤ 0, so a < 0. 
      have h6 : a < 0 := by 
        by_contra h7 
        push_neg at h7 
        have : a = 0 := by linarith 
        contradiction 
      have h14 : - (3 - 3 * a) ≥ 2 * a := by 
        have h7' : - (3 - 3 * a) / (2 * a) ≤ 1 := h7 
        apply (div_le_iff_of_neg' (by linarith)).mp at h7' 
        linarith 
      nlinarith 
  constructor
  · linarith [h5]
  · linarith [h6]