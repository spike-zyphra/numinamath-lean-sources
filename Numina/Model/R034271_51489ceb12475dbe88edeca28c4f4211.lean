import Mathlib

theorem number_theory_274681 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hab : a * b = 2010) (h : a > b) :
    IsLeast {x | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a * b = 2010 ∧ a > b ∧ x = a - b} 37 := by
  constructor
  · -- Show 37 is achievable using the pair (67, 30)
    use 67, 30
    all_goals norm_num
    all_goals linarith
  · -- Show 37 is the smallest such value
    intro x hx
    rcases hx with ⟨a, b, ha, hb, hab, h1, hx⟩
    by_contra h
    push_neg at h
    -- From `h` we know that $x < 37$, which with $x = a-b$ gives $a-b < 37$.
    -- To show a contradicts, we need to analyze the factors of 2010
    have h3 : a - b < 37 := by
      omega
    -- To show contradiction, we need to find factors of 2010 
    -- and show no pair satisfies a - b < 37.
    -- This implies we must check all possible pairs of factors.
    have h4 : b ≤ 44 := by
      have h5 : a * b = 2010 := hab
      have h6 : a > b := h1
      have h7 : a ≥ b + 1 := by
        omega
      have h8 : (b + 1) * b ≤ a * b := by
        nlinarith [h7, show b ≤ a by nlinarith]
      have h9 : (b + 1) * b ≤ 2010 := by
        nlinarith [h8, hab]
      nlinarith
    have h5 : a ≤ 2010 := by
      nlinarith [hab, show b ≥ 1 by nlinarith]
    interval_cases b <;> try { omega } <;> try { 
      have : a ≤ 2010 := by nlinarith
      interval_cases a <;> omega 
    }
    <;> try { 
      tauto 
    }
    <;> norm_num at hab h1 hx 
    <;> try { 
      tauto 
    }
    <;> try { 
      nlinarith 
      all_goals nlinarith 
    }