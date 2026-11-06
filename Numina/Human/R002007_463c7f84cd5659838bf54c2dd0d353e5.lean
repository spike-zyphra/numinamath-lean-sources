import Mathlib

/- The positive integer $m$ is a multiple of $101$, and the positive integer $n$ is a multiple of $63$. Their sum is $2018$. Find $m - n$. -/
theorem number_theory_54394 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (h₀ : 101 ∣ m) (h₁ : 63 ∣ n)
    (h₂ : m + n = 2018) : m - n = 2 := by 
  -- Extract everything from the assumptions to use in calculations
  omega