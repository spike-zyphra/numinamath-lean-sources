import Mathlib

open Real

/- (4) The smallest positive integer $a$ that makes the inequality $\frac{1}{n+1}+\frac{1}{n+2}+\cdots+\frac{1}{2 n+1}<a-2007 \frac{1}{3}$ hold for all positive integers $n$ is $\qquad$. -/
theorem inequalities_131136 :
  let f := fun (n : ℕ) => ∑ i ∈ Finset.range (n + 1), (1 : ℚ) / (n + 1 + i);
  IsLeast {a : ℕ | ∀ n : ℕ, f n < a - 2007} 2009 := by
  intro f
  -- Show f is strictly decreasing
  have f_anti : StrictAnti f
  · apply strictAnti_nat_of_succ_lt
    intro n
    simp [f]
    rw [Finset.sum_range_succ' _ n]
    conv => enter [2, 1, 2, k]; rw [Nat.cast_add, Nat.cast_one, add_assoc, add_comm _ 1, ←add_assoc, ←add_assoc]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, add_assoc (∑ k ∈ _, _) _ _]
    apply add_lt_add_left
    calc
      _ = (2 * (n : ℚ) + 2)⁻¹ + (2 * (n : ℚ) + 3)⁻¹ := by rw [Nat.cast_add]; congr 1 <;> ring
      _ < 2 * (2 * (n : ℚ) + 2)⁻¹ := by
        rw [two_mul (2 * (n : ℚ) + 2)⁻¹]
        apply add_lt_add_left
        rw [inv_lt_inv₀ (by positivity) (by positivity)]
        linarith
      _ = 2 * (2 * ((n : ℚ) + 1))⁻¹ := by ring
      _ = _ := by rw [mul_inv]; ring
  -- Show f 0 = 1
  have hf0 : f 0 = 1
  · simp [f]
  constructor
  -- Use f strictly decreasing to show a = 2009 works
  · intro n
    calc
      f n ≤ 1 := by rw [←hf0]; apply f_anti.antitone (Nat.zero_le n)
      _ < 2009 - 2007 := by norm_num
  -- Show that a > 2008, so a = 2009 is the least a
  intro a h
  specialize h 0
  rw [hf0] at h
  have : 2008 < (a : ℚ)
  · linarith
  norm_cast at this