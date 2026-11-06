import Mathlib

open Real

theorem inequalities_158379 (n : ℕ) (hn : 0 < n) (a b : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hsum : ∑ i, a i = 1 ∧ ∑ i, b i = 1) :
    ∑ i, (a i)^2 / b i ≥ 1 := by
  -- Extract the hypotheses that the sum of a_i = 1 and sum of b_i = 1
  have h1 : ∑ i, a i = 1 := hsum.left
  have h2 : ∑ i, b i = 1 := hsum.right
  -- For each index i, show that (a_i)^2 / b_i >= 2 * a_i - b_i
  have h3 : ∀ i, (a i) ^ 2 / (b i) ≥ (2 * (a i) - (b i)) := by
    intro i
    -- Get the positivity of a_i and b_i from the hypotheses
    have hb' : 0 < b i := hb i
    have ha' : 0 < a i := ha i
    -- We need to prove (a_i)^2 / b_i >= 2 * a_i - b_i.
    -- Multiply both sides by the positive b_i.
    have h4 : (a i) ^ 2 ≥ (2 * (a i) - (b i)) * (b i) := by
      nlinarith [sq_nonneg ((a i) - (b i)), mul_pos (show 0 < (a i) by linarith) (show 0 < (b i) by linarith)]
    -- We have the multiplicative version, now convert to division by dividing by positive b_i
    have h5 : (a i) ^ 2 / (b i) ≥ (2 * (a i) - (b i)) := by
      apply (le_div_iff₀ (by linarith)).mpr
      linarith
    linarith

  -- Sum over all i, using the fact that sum of a_i = 1 and sum of b_i = 1
  -- First, show that the sum of the left side is greater than or equal to the sum of the right side
  have h4 : ∑ i, (a i) ^ 2 / (b i) ≥ ∑ i, (2 * (a i) - (b i)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact h3 i

  -- Compute the sum of the right side
  have h5 : ∑ i, (2 * (a i) - (b i)) = 2 * (∑ i, (a i)) - (∑ i, (b i)) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
    <;> ring

  -- Substitute the computed sums into the expression
  have h6 : ∑ i, (2 * (a i) - (b i)) = 1 := by
    rw [h5]
    rw [h1, h2]
    all_goals norm_num

  -- Transitivity: sum of left side >= sum of right side = 1, therefore sum of left side >= 1
  linarith [h4, h6]