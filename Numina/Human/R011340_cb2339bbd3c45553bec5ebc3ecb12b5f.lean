import Mathlib

open Real

/- Prove that the arithmetic mean $a$ of $x_{1}, \ldots, x_{n}$ satisfies

$$
\left(x_{1}-a\right)^{2}+\cdots+\left(x_{n}-a\right)^{2} \leqslant \frac{1}{2}\left(\left|x_{1}-a\right|+\cdots+\left|x_{n}-a\right|\right)^{2} .
$$ -/
theorem inequalities_238801 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ) (a : ℝ)
    (ha : a = ∑ i : Fin n, x i / n) :
    ∑ i : Fin n, (x i - a) ^ 2 ≤ (1 / 2) * (∑ i : Fin n, |x i - a|) ^ 2 := by
  set y : Fin n → ℝ := λ i => x i - a with hy
  -- show that 0 = ∑ i, y i
  replace ha : ∑ i, y i = 0 := by
    rw [hy]
    simp
    calc -- replace y i with x i - a
      ∑ x_1 : Fin n, x x_1 - (n : ℝ) * a = (n : ℝ) * (∑ x_1 : Fin n, x x_1) / (n : ℝ) - (n : ℝ) * a := by simp; rw [mul_div_cancel_left₀]; norm_cast; linarith only [hn]
      _ = (n : ℝ) * ((∑ x_1 : Fin n, x x_1) / (n : ℝ)) - (n : ℝ) * a := by ring_nf
      _ = (n : ℝ) * (∑ x_1 : Fin n, x x_1 / (n : ℝ)) - (n : ℝ) * a := by congr; rw [Finset.sum_div]
      _ = (n : ℝ) * a - (n : ℝ) * a := by rw [ha]
      _ = 0 := by ring_nf
  -- suffice to show that ∑ i, y i ^ 2 = 1 / 2 * (∑ i, |y i|) ^ 2
  suffices h : ∑ i, y i ^ 2 ≤ 1 / 2 * (∑ i, |y i|) ^ 2 by
    rw [hy] at h
    simp at h ⊢
    exact h
  -- divide the set of i into positive and non-positive parts
  set Set_pos : Finset (Fin n) := {i | 0 < y i} with hpos
  set Set_neg : Finset (Fin n) := {i | y i ≤ 0} with hneg
  
  -- inequality of positive part
  -- show that ∑ i in Set_pos, y i ^ 2 ≤ (∑ i in Set_pos, y i) ^ 2
  have ineq_pos : ∑ i in Set_pos, y i ^ 2 ≤ (∑ i in Set_pos, y i) ^ 2 := by 
    apply Finset.sum_sq_le_sq_sum_of_nonneg -- exact the form of the inequality
    -- show that 0 ≤ y i, ∀ i ∈ Set_pos
    rw [hpos]
    simp
    intro i hi
    linarith only [hi]
  -- show that ∑ i in Set_pos, |y i| = ∑ i in Set_pos, y i
  have sum_pos : ∑ i in Set_pos, |y i| = ∑ i in Set_pos, y i := by 
    apply Finset.sum_congr
    -- show the set of i is the same
    . simp
    -- show that |y i| = y i, ∀ i ∈ Set_pos
    . simp [hpos]
      intro i hi
      linarith only [hi]
  
  -- non-positive part
  -- show that ∑ i in Set_neg, y i ^ 2 ≤ (∑ i in Set_neg, y i) ^ 2
  have ineq_neg : ∑ i in Set_neg, y i ^ 2 ≤ (∑ i in Set_neg, y i) ^ 2 := by 
    -- change the term of sum to positive
    suffices h : ∑ i in Set_neg, (-y i) ^ 2 ≤ (∑ i in Set_neg, -y i) ^ 2 by 
      rw [Finset.sum_neg_distrib] at h
      simp at h ⊢
      exact h
    -- similar to the positive part
    apply Finset.sum_sq_le_sq_sum_of_nonneg
    simp [hneg]
  -- show that ∑ i in Set_neg, |y i| = ∑ i in Set_neg, y i
  have sum_neg : ∑ i in Set_neg, |y i| = -∑ i in Set_neg, y i := by 
    rw [<-Finset.sum_neg_distrib]
    apply Finset.sum_congr
    . simp -- show the set of i is the same
    . simp [hneg] -- show that |y i| = -y i, ∀ i ∈ Set_neg
  
  -- show that sum of Set_pos and Set_neg is Fin n
  have pos_plus_neg (f : Fin n → ℝ) : ∑ i in Set_pos, f i + ∑ i in Set_neg, f i = ∑ i : Fin n, f i := by
    rw [<-Finset.sum_union]
    rw [Finset.sum_congr]
    -- easily show that the term of sum is the same
    pick_goal 2
    . intro x _
      simp
    -- show that the union of Set_pos and Set_neg is Fin n
    . ext x
      simp [hpos, hneg]
      have h := le_or_lt (y x) 0
      tauto
    -- show that the intersection of Set_pos and Set_neg is empty
    . rw [Finset.disjoint_left] -- equivalent to a element of Set_pos
      intro x hx_pos
      rw [hpos] at hx_pos
      rw [hneg]
      simp at hx_pos ⊢
      exact hx_pos
  
  -- calculate the sum of |y i|
  -- show that ∑ i in Set_pos, |y i| = ∑ i in Set_neg, |y i|
  have pos_eq_neg : ∑ i in Set_pos, |y i| = ∑ i in Set_neg, |y i| := by 
    rw [sum_pos, sum_neg]
    have hsum := pos_plus_neg (λ i => y i) -- apply f i = y i
    rw [ha] at hsum
    linarith only [hsum]
  -- show the relation between ∑ i in Set_pos, |y i| and ∑ i : Fin n, |y i|
  have pos_eq_half : ∑ i in Set_pos, |y i| = 1 / 2 * ∑ i : Fin n, |y i| := by 
    have hsum := pos_plus_neg (λ i => |y i|)
    linarith only [hsum, pos_eq_neg] -- combine with the previous result
  
  -- finally calculate the desired inequality
  calc
    ∑ i, y i ^ 2 = ∑ i in Set_pos, y i ^ 2 + ∑ i in Set_neg, y i ^ 2 := by rw [pos_plus_neg]
    _ ≤ (∑ i in Set_pos, y i) ^ 2 + (∑ i in Set_neg, y i) ^ 2 := by nlinarith only [ineq_pos, ineq_neg]
    _ = (∑ i in Set_pos, |y i|) ^ 2 + (∑ i in Set_neg, |y i|) ^ 2 := by rw [sum_pos, sum_neg]; ring_nf
    _ = 1 / 2 * (∑ i : Fin n, |y i|) ^ 2 := by rw [<-pos_eq_neg, pos_eq_half]; ring_nf
  