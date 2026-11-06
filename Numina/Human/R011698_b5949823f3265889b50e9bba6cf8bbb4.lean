import Mathlib

open Real

/- ## Task 25/76

Solve the equation $\sin ^{4} x+\cos ^{7} x=1$ for real numbers $x$. -/
theorem number_theory_155969 :
    {x : ℝ | sin x ^ 4 + cos x ^ 7 = 1} = {π / 2 + k * π | k : ℤ} ∪ {2 * k * π | k : ℤ} := by
  ext x
  -- {π / 2 + k * π | k : ℤ} is the set of points where cos x = 0
  -- {2 * k * π | k : ℤ} is the set of points where cos x = 1
  have ⟨H₁, H₂⟩ : (x ∈ {π / 2 + k * π | k : ℤ} ↔ cos x = 0) ∧ (x ∈ {2 * k * π | k : ℤ} ↔ cos x = 1) := by
    -- Use the lemmas `Real.cos_eq_zero_iff` and `Real.cos_eq_one_iff` to prove the biimplication
    constructor <;> [simp [Real.cos_eq_zero_iff]; simp [Real.cos_eq_one_iff]]
    all_goals
      congrm ∃ k, ?_
      constructor
      all_goals
        rintro rfl
        ring
  -- Simplify the equation using the biimplications from `H₁` and `H₂`
  rw [Set.mem_union, H₁, H₂]
  clear H₁ H₂
  simp
  -- Rewrite the equation in terms of `cos x` (get rid of `sin x`)
  rw [show sin x ^ 4 = (sin x ^ 2) ^ 2 by ring,
        sin_sq,
        show (1 - cos x ^ 2) ^ 2 + cos x ^ 7 = 1 + cos x ^ 2 * (cos x ^ 5 + cos x ^ 2 - 2) by ring]
  simp
  apply or_congr_right
  -- Now we only need to prove that `cos x ^ 5 + cos x ^ 2 - 2 = 0 ↔ cos x = 1`
  constructor
  . intro h
    simp at h
    -- We have `cos x ^ n ≤ 1` since `|cos x| ≤ 1`
    have H (n : ℕ) : cos x ^ n ≤ 1 := by
      apply le_of_abs_le
      simp
      exact pow_le_one₀ (by simp) (abs_cos_le_one x)
    -- So by `linarith`, we have `cos x ^ 5 = 1` and `cos x ^ 2 = 1`
    have ⟨H₁, H₂⟩ : cos x ^ 5 = 1 ∧ cos x ^ 2 = 1 := by
      constructor
      all_goals
        linarith [H 5, H 2]
    -- Therefore, we have `cos x = 1`
    calc cos x
      _ = cos x * (cos x ^ 2) ^ 2 := by simp [H₂]
      _ = cos x ^ 5 := by ring
      _ = 1 := H₁
  . -- If `cos x = 1`, then `cos x ^ 5 + cos x ^ 2 - 2 = 0` trivially holds
    rintro h
    norm_num [h]
