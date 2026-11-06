import Mathlib

/- If $x$ and $ \sqrt { x ^ { 2 } + 2025 } $ are positive integers, find the minimum value of $x$. -/
theorem number_theory_623167 :
    IsLeast {x : ℕ | x > 0 ∧ ∃ z : ℕ, z > 0 ∧ z = √(x ^ 2 + 2025)} 24 := by
  constructor
  . -- We check that 24 is a solution.
    -- Since 24 ^ 2 + 2025 = 51 ^ 2
    simp
    use 51, by simp
    norm_num
    rw [show (2601 : ℝ) = 51 ^ 2 by norm_num]
    simp
  . -- We show that any solution is at least 24.
    intro x ⟨hx, z, hz, h⟩
    -- Cancel the square root.
    apply_fun (· ^ 2) at h
    simp [show 0 ≤ (x ^ 2 + 2025 : ℝ) by positivity] at h
    norm_cast at h
    -- So z ^ 2 - x ^ 2 = 2025
    replace h : z ^ 2 - x ^ 2 = 2025 := by simp [h]
    -- x < z
    have hz₀ : x ^ 2 < z ^ 2 := Nat.lt_of_sub_eq_succ h
    replace hz₀ : x < z := lt_of_pow_lt_pow_left' 2 hz₀
    -- (z - x) (z + x) = 2025
    rw [Nat.sq_sub_sq] at h
    -- z + x ∣ 2025
    have h₁ : z + x ∣ 2025 := Dvd.intro (z - x) h
    -- So z + x is a divisor of 2025
    replace h₁ : z + x ∈ Nat.divisors 2025 := by simp [h₁]
    -- So z - x = 2025 / (z + x)
    have h₂ : z - x = 2025 / (z + x) := by rw [← h]; simp [show z + x ≠ 0 by omega]
    -- z - x < z + x
    have h₃ : z - x < z + x := by omega
    -- x = (z + x - (z - x)) / 2
    have h₄ : x = (z + x - (z - x)) / 2 := by omega
    rw [h₂] at h₃ h₄
    rw [h₄]
    -- We generalize z + x to t.
    -- We check all the cases of t ∈ Nat.divisors 2025 by `native_decide`.
    generalize z + x = t at *
    clear * - h₁ h₃
    revert t
    native_decide
