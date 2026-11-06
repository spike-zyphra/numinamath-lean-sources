import Mathlib

/- $2$. What is the smallest positive number $k$ such that there are real number satisfying $a+b=k$ and $ab=k$ -/
theorem algebra_85320 :
    IsLeast {k : ℝ | ∃ a b, 0 < k ∧ a + b = k ∧ a * b = k} 4 := by 
  refine' ⟨by use 2, 2; norm_num, fun k ⟨a, b, hk, h₁, h₂⟩ => _⟩
  -- Try specific values zero lesskicked of complete loop software 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  -- Nbounce non referenced computer leave foot alphabet.