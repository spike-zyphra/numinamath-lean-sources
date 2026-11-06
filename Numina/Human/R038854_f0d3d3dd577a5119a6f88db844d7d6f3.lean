import Mathlib

/- 11.6. The sequence of numbers $a_{1}, a_{2}, \ldots, a_{2022}$ is such that $a_{n}-a_{k} \geqslant$ $\geqslant n^{3}-k^{3}$ for any $n$ and $k$ such that $1 \leqslant n \leqslant 2022$ and $1 \leqslant k \leqslant$ $\leqslant 2022$. Moreover, $a_{1011}=0$. What values can $a_{2022}$ take?

(N. Agakhanov) -/
theorem inequalities_129190 (a : ℕ → ℝ) (h : ∀ n k, 1 ≤ n → n ≤ 2022 → 1 ≤ k → k ≤ 2022 → a n - a k ≥ n ^ 3 - k ^ 3)
    (ha : a 1011 = 0) :
    a 2022 = 2022 ^ 3 - 1011 ^ 3 := by
      -- Applying the condition for n = 2022 and k = 1011, we get a₂₀₂₂ = a₂₀₂₂ - a₁₀₁₁ ≥ 2022^3 - 1011^3
      have: a 2022 ≥ 2022^3 - 1011^3 := by calc
        a 2022 = a 2022 - a 1011 := by rw [ha, sub_zero]
        _ ≥ 2022^3 - 1011^3 := by
          apply h
          all_goals norm_num
      -- Applying the condition for n = 1011 and k = 2022, we get -a₂₀₂₂ = a₁₀₁₁ - a₂₀₂₂ ≥ 1011^3 - 2022^3
      have: -a 2022 ≥ 1011^3 - 2022^3 := by calc
        -a 2022 = a 1011 - a 2022 := by rw [ha, zero_sub]
        _ ≥ 1011^3 - 2022^3 := by
           apply h
           all_goals norm_num
      -- Thus a₂₀₂₂ ≥ 2022^3 - 1011^3 ≥ a₂₀₂₂, and so a₂₀₂₂ = 2022^3 - 1011^3
      linarith