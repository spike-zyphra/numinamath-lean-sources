import Mathlib

/- For what single digit $n$ does 91 divide the 9 -digit number $12345 n 789$ ?-/
theorem number_theory_609861 :
    {n : ℕ | n ≤ 9 ∧ 91 ∣ 123450789 + 1000 * n} = {7} := by
  -- Simplify the goal into two parts.
  ext n
  simp
  apply Iff.intro
  . -- Show that if the 9-digit number 12345n789 is divisible by 91, then n = 7.
    rintro ⟨h₀, h₁⟩
    omega
  . -- Show that 123457789 is divisible by 91.
    intro hn
    norm_num [hn]
    
