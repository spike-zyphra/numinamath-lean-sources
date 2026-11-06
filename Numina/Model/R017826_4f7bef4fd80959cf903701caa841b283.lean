import Mathlib

theorem algebra_234515 (a b c : ℝ) (ha : a + b ∈ Set.Icc 0 1) (hb : b + c ∈ Set.Icc 0 1)
    (hc : c + a ∈ Set.Icc 0 1) :
    a^2 + b^2 + c^2 ≤ 1 := by 
  have h2 : 0 ≤ a + b := by 
    have h : a + b ∈ Set.Icc (0 : ℝ) 1 := ha
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  have h4 : 0 ≤ b + c := by 
    have h : b + c ∈ Set.Icc (0 : ℝ) 1 := hb
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  have h6 : 0 ≤ c + a := by 
    have h : c + a ∈ Set.Icc (0 : ℝ) 1 := hc
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  have h8 : a + b ≤ 1 := by 
    have h : a + b ∈ Set.Icc (0 : ℝ) 1 := ha
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  have h10 : b + c ≤ 1 := by 
    have h : b + c ∈ Set.Icc (0 : ℝ) 1 := hb
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  have h12 : c + a ≤ 1 := by 
    have h : c + a ∈ Set.Icc (0 : ℝ) 1 := hc
    simp at h ⊢
    all_goals 
      try { linarith [h.1, h.2] } 
      <;> try { tauto }
  -- Express a, b, c in terms of the sums 
  have eq1 : a = ( (a + b) - (b + c) + (c + a) ) / 2 := by 
    ring_nf
  have eq2 : b = ( (a + b) + (b + c) - (c + a) ) / 2 := by 
    ring_nf
  have eq3 : c = ( - (a + b) + (b + c) + (c + a) ) / 2 := by 
    ring_nf
  rw [eq1, eq2, eq3]
  -- Now we need to show that the quadratic form is ≤ 1, using bounds on the sums
  nlinarith [sq_nonneg (a + b - 1/2), sq_nonneg (b + c - 1/2), sq_nonneg (c + a - 1/2),
            mul_nonneg (show (0 : ℝ) ≤ a + b by linarith [h2, h8]) (show (0 : ℝ) ≤ 1 - (a + b) by linarith [h2, h8]),
            mul_nonneg (show (0 : ℝ) ≤ b + c by linarith [h4, h10]) (show (0 : ℝ) ≤ 1 - (b + c) by linarith [h4, h10]),
            mul_nonneg (show (0 : ℝ) ≤ c + a by linarith [h6, h12]) (show (0 : ℝ) ≤ 1 - (c + a) by linarith [h6, h12])]