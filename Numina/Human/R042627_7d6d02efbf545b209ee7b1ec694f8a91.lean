import Mathlib

/- 12. (NET 1) ${ }^{\mathrm{IMO} 2}$ Find two positive integers $a, b$ such that none of the numbers $a, b, a+b$ is divisible by 7 and $(a+b)^{7}-a^{7}-b^{7}$ is divisible by $7^{7}$. -/
theorem number_theory_23912 :
    ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ ¬(7 ∣ a) ∧ ¬(7 ∣ b) ∧ ¬(7 ∣ a + b) ∧
      7^7 ∣ (a + b)^7 - a^7 - b^7 := by 
    -- Trying $a=1$ we easily find the example $(a, b)=(1,18)$.
    use 1, 18
    -- Verify the conditions directly with numerical checks。
    norm_num