import Mathlib

/- 1. Let $\{x\}$ denote the fractional part of the real number $x$. Given $a=(5 \sqrt{2}+7)^{2017}$. Then $a\{a\}=$ $\qquad$ . -/
theorem number_theory_308564 (a : ℝ) (ha : a = (5 * √2 + 7) ^ 2017) :
    a * Int.fract a = 1 := by
  -- Set α := 5 * √2 + 7, β := -5 * √2 + 7
  let α := 5 * √2 + 7
  let β := -5 * √2 + 7
  -- So α and β are the roots of the quadratic equation x^2 - 14x + 1 = 0
  -- They satisfy α + β = 14 and α * β = -1
  have hsum : α + β = 14 := by ring
  have hprod : α * β = -1 := by ring_nf; norm_num
  have hα : α ^ 2 = 14 * α + 1 := by
    obtain hβ : β = 14 - α := by linear_combination hsum
    rw [hβ] at hprod
    linear_combination -hprod
  have hβ : β ^ 2 = 14 * β + 1 := by
    obtain hα : α = 14 - β := by linear_combination hsum
    rw [hα] at hprod
    linear_combination -hprod
  -- We have 0 ≤ -β < 1 since 1.4 ≤ √2 < 1.6
  have hβ₁ : 0 ≤ -β := by
    simp [β]
    suffices 7 / 5 ≤ √2 by linarith only [this]
    exact Real.le_sqrt_of_sq_le (by norm_num)
  have hβ₂ : -β < 1 := by
    simp [β]
    suffices √2 < 8 / 5 by linarith only [this]
    exact (Real.sqrt_lt' (by simp)).mpr (by norm_num)
  -- So α ^ n + β ^ n satisfies a linear recurrence relation
  -- x_{n+2} = 14 * x_{n+1} + x_n
  have H₁ (n : ℕ) : α ^ (n + 2) + β ^ (n + 2) = 14 * (α ^ (n + 1) + β ^ (n + 1)) + (α ^ n + β ^ n) := by
    repeat rw [pow_add]
    simp [hα, hβ]
    ring
  -- We can show that α ^ n + β ^ n is an integer for all n
  have H₂ (n : ℕ) : ∃ z : ℤ, α ^ n + β ^ n = z := by
    -- We use two-step induction to show that α ^ n + β ^ n is an integer for all n
    induction n using Nat.twoStepInduction with
    | zero => exact ⟨2, by ring⟩ -- α ^ 0 + β ^ 0 = 2
    | one => exact ⟨14, by ring⟩ -- α ^ 1 + β ^ 1 = 14
    | more n ih₁ ih₂ =>
      -- If α ^ n + β ^ n and α ^ (n+1) + β ^ (n+1) are integers, then so is α ^ (n+2) + β ^ (n+2) by the recurrence relation
      rcases ih₁ with ⟨z₁, hz₁⟩
      rcases ih₂ with ⟨z₂, hz₂⟩
      use z₁ + 14 * z₂
      simp [H₁, hz₁, hz₂]
      ring
  -- We have {a} = (-β) ^ 2017 since α ^ 2017 + β ^ 2017 is an integer with
  have H₃ : Int.fract a = (-β) ^ 2017 := by
    -- It suffices to show that 0 ≤ (-β) ^ 2017 < 1 and a - (-β) ^ 2017 is an integer
    rw [Int.fract_eq_iff]
    refine ⟨?_, ?_, ?_⟩
    . exact pow_nonneg hβ₁ 2017
    . exact pow_lt_one₀ hβ₁ hβ₂ (by simp)
    . -- We have α ^ 2017 + β ^ 2017 is an integer
      rcases H₂ 2017 with ⟨z, hz⟩
      use z
      rw [← hz, ha, Odd.neg_pow (by decide)]
      simp [α]
  -- So a * {a}
  -- = α ^ 2017 * (-β) ^ 2017
  -- = (α * (-β)) ^ 2017
  -- = 1 ^ 2017
  -- = 1
  calc a * Int.fract a
    _ = α ^ 2017 * (-β) ^ 2017 := by rw [H₃, ha]
    _ = (α * (-β)) ^ 2017 := (mul_pow _ _ _).symm
    _ = 1 ^ 2017 := by congr; linear_combination -hprod
    _ = 1 := by simp
