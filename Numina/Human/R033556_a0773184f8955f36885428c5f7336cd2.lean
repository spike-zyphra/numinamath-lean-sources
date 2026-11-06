import Mathlib

open Real Set
open scoped BigOperators

/- The value range of the function $y=\cos 2x-8\cos x$ is __________. -/
theorem algebra_9053 : range (λ x => cos (2 * x) - 8 * cos x) = {y | -7 ≤ y ∧ y ≤ 9} := by

  -- Simplify the expression `cos(2x) - 8 * cos(x)`
  have h₀ x : cos (2 * x) - 8 * cos x = 2 * (2 - cos x) ^ 2 - 9 :=
      calc
      cos (2 * x) - 8 * cos x = 2 * cos x ^ 2 - 1 - 8 * cos x := by rw [Real.cos_two_mul x]
                            _ = 2 * (2 - cos x) ^ 2 - 9 := by ring

  -- Simplify the set notation
  dsimp [Set.range]
  ext y
  constructor <;> intro h

  -- Prove the forward direction: If y is in the range, then -7 ≤ y ≤ 9
  · rcases h with ⟨x, hx⟩
    simp_all
    generalize hz : (cos x - 2) = z
    -- Derive bounds for `z` using the properties of the cosine function
    have : -3 ≤ z := by nlinarith [Real.neg_one_le_cos x]
    have : z ≤ -1 := by nlinarith [Real.cos_le_one x]
    constructor <;> nlinarith

  -- Prove the backward direction: If -7 ≤ y ≤ 9, then y is in the range
  . simp_all
    -- Use the arccosine function to find an `x` such that `cos(2x) - 8 * cos(x) = y`
    use arccos (2 - (sqrt ((y + 9) / 2)))
    generalize ha : 2 - √((y + 9) / 2) = a

    -- Show that `a` is within the domain of `arccos`
    have ha₀ : -1 ≤ a := by
      rw [← ha]
      simp; norm_num
      have h₁ : 0 ≤ (18:ℝ) := by linarith
      have : y + 9 ≤ 18 := by linarith
      rw [← Real.sqrt_le_sqrt_iff h₁] at this
      rw [div_le_iff₀]
      have : √(y + 9) ≤ 3 * √2 := by
        calc
        √(y + 9) ≤ √18 := by linarith
               _ = √((3 ^ 2) * 2) := by norm_num
               _ = 3 * √2 := by simp
      exact this
      norm_num

    -- Use similar techniques to derive the bound
    have ha₁ : a ≤ 1 := by
      rw [← ha]
      simp; rw [← tsub_le_iff_left, le_div_iff₀]; norm_num
      have : -7 + 9 ≤ y + 9 := by linarith
      have : √(-7 + 9) ≤ √(y + 9) := by simp [sqrt_le_sqrt this]
      have : √2 ≤ √(y + 9) := by
        calc
        √2 = √(-7 + 9) := by norm_num
         _ ≤ √(y + 9) := by nlinarith
      exact this
      norm_num

    -- Use the properties of `arccos` to show that `cos(2x) - 8 * cos(x) = y`
    rw [cos_arccos ha₀ ha₁, ← ha]
    norm_num
    rw [div_pow, sq_sqrt, sq_sqrt]
    have : 2 * ((y + 9) / 2) - 9 = y := by ring
    exact this
    linarith
    linarith
