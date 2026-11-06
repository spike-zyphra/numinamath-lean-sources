import Mathlib

open Finset

theorem algebra_109627 {A : ℝ} (hA : A = 53 * ∑ i ∈ range 2013, ((1:ℝ) / ((i + 1) * (i + 2)))) : A = 2013/38 ∧ (∃ a b c d e : ℕ, (A = (a * b * c : ℝ) / (d * e) ∧ (Nat.digits 10 a).sum + (Nat.digits 10 b).sum + (Nat.digits 10 c).sum = (Nat.digits 10 d).sum + (Nat.digits 10 e).sum)) := by 
  
  --We calculate the sum $\frac{1}{1 \times 2}+\frac{1}{2 \times 3}+\cdots+\frac{1}{2013 \times 2014}$ by simple induction.
  have Aeq: A = 2013/38 := by 
    have lem: ∀ m:ℕ, ∑ i ∈ range (m+1), ( (1:ℝ) / ((i + 1) * (i + 2))) = 1-1/(m+2) := by
      intro m
      induction' m with m hm

      field_simp
      norm_num

      have eq: ∑ i ∈ range (m + 1 + 1), (1:ℝ) / ((i + 1) * (↑i + 2)) = ∑ i ∈ range (m + 1), (1:ℝ) / ((↑i + 1) * (↑i + 2)) + 1 / ((↑(m + 1)+1) * (↑(m + 1) + 2)) := by 
        exact sum_range_succ (fun x => (1:ℝ) / ((↑x + 1) * (↑x + 2))) (m + 1)
      rw [eq,hm]
      field_simp
      ring_nf
    have tmp : ∑ i ∈ range (2012+1), ( (1:ℝ) / ((i + 1) * (i + 2))) = 1-1/(2012+2) := by apply lem
    have : 2012 + 1 = 2013 := by norm_num
    rw [this] at tmp
    have : (2012:ℝ) + 2 = 2014 := by norm_num
    rw [this] at tmp
    rw [tmp] at hA
    rw [hA]
    norm_num
  
  constructor

  exact Aeq

  -- These 5 numbers satisfy the assumption.
  use 3, 11, 61, 2, 19
  simp [Aeq]
  norm_num
