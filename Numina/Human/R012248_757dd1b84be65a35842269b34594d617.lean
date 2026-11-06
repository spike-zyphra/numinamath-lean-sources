import Mathlib

open Finset

/- 2. Find the smallest possible value of the function

$$
f(x)=|x+1|+|x+2|+\ldots+|x+100|
$$

$(25$ points. $)$ -/
theorem algebra_193731 :
    IsLeast {∑ i ∈ Icc (1 : ℕ) 100, |x + i| | x : ℝ} 2500 := by
  constructor
  . -- We first check that 2500 is achievable.
    -- We can achieve this by taking x = -50.
    use -50
    -- We rewrite the sum in terms of ℤ to avoid issues with ℝ.
    suffices H : ∑ i ∈ Icc (1 : ℕ) 100, |-50 + (i : ℤ)| = 2500 by
      rify at H
      exact H
    -- We now compute the sum.
    native_decide
  . -- We now show that 2500 is the minimum possible value.
    rintro - ⟨x, rfl⟩
    -- We first show that |a - b| ≤ |x + a| + |x + b| for all a, b : ℕ.
    have lem (a b : ℝ) : |a - b| ≤ |x + a| + |x + b| := by
      convert abs_sub (x + a) (x + b) using 2
      ring
    -- We use symmetry to write ∑ i ∈ [1, 100], |x + i| as ∑ i ∈ [1, 100], |x + (101 - i)|.
    have H := Finset.sum_Ico_reflect (fun i => |x + i|) 1 (show 101 ≤ 101 + 1 by simp)
    simp [show Ico 1 101 = Icc 1 100 by rfl] at H
    calc ∑ i ∈ Icc (1 : ℕ) 100, |x + i|
      -- We replicate the sum.
      _ = ((∑ i ∈ Icc (1 : ℕ) 100, |x + i|) + (∑ i ∈ Icc (1 : ℕ) 100, |x + i|)) / 2 := by ring
      -- We change one of the sums to use the symmetry.
      _ = ((∑ i ∈ Icc (1 : ℕ) 100, |x + i|) + (∑ i ∈ Icc (1 : ℕ) 100, |x + (101 - i : ℕ)|)) / 2 := by rw [H]
      -- We distribute the sum.
      _ = (∑ i ∈ Icc (1 : ℕ) 100, (|x + i| + |x + (101 - i : ℕ)|)) / 2 := by rw [Finset.sum_add_distrib]
      -- We use the lemma to bound the sum.
      _ ≥ (∑ i ∈ Icc (1 : ℕ) 100, (|(i : ℝ) - (101 - i : ℕ)|)) / 2 := by gcongr; simp [lem]
      -- Rewrite the sum in terms of ℤ.
      _ = (∑ i ∈ Icc (1 : ℕ) 100, (|(i : ℤ) - (101 - i : ℕ)|)) / (2 : ℝ) := by rify
      -- Compute the sum.
      _ = (5000 : ℤ) / (2 : ℝ) := by congrm (?_ : ℤ) / (2 : ℝ); native_decide
      _ = 2500 := by norm_num
