import Mathlib

/- $Problem 2. a) Show that for any real numbers $a, b, c$ the relation $|a+b|+|a+c| \geq|b-c|$ holds.

b) Prove that for any real number $x$ the inequality holds:

$$
|x+1|+|x+2|+|x+3|+\ldots+|x+2014| \geq 1007^{2}
$$

Liliana Puţ, Gazeta Matematică nr. 11/2014 -/

open Finset Function

theorem algebra_109249 (a b c : ℝ) (x : ℝ):
    (abs (a + b) + abs (a + c) ≥ abs (b - c)) ∧ (∑ i ∈ Finset.range 2014, abs (x + i + 1) ≥ 1007^2 ) := by 
  constructor
  -- For part (a)
  · -- ∀ (m n : ℝ), |m + n| ≤ |m| + |n|
    have ineq_aux : ∀ (m n : ℝ), |m + n| ≤ |m| + |n| := by
      intro m n
      exact abs_add_le m n
    obtain h1 := ineq_aux (a + b) (- (a + c))
    ring_nf at h1
    have eq_aux : |-a - c| = |a + c| := by 
      refine abs_eq_abs.mpr ?_
      right;ring_nf
    rw [eq_aux] at h1
    linarith
  -- For part (b)
  · -- ∀ k ∈ {1,2,...,1007}, |x + k| + |x + k + 1007| ≥ 1007
    have ineq_aux : ∀ k ∈ range 1007, |x + k + 1| + |x + k + 1007 + 1| ≥ 1007 := by 
      intro k hk
      obtain h1 := abs_add_le (x + k + 1007 + 1) (-(x + k + 1))
      ring_nf at h1
      simp at h1
      ring_nf
      have eq_aux : |-1 + (-x - ↑k)| = |1 + x + k| := by 
        refine abs_eq_abs.mpr ?_
        right;ring_nf
      rw [eq_aux] at h1
      linarith
    -- reordering the sum to get the equality
    have eq_aux : (∑ i ∈ range 2014, |x + ↑i + 1| = 
      ∑ k ∈ range 1007, (|x + k + 1| + |x + k + 1007 + 1|)) := by 
      rw [Finset.sum_add_distrib]
      have disj_aux : Disjoint (range 1007) ((range 2014)\ (range 1007)):= by 
        apply Finset.disjoint_right.mpr
        intro a ha
        simp at ha
        simp
        obtain ⟨h1, h2⟩ := ha
        exact h2
      have disu_aux : disjUnion (range 1007) ((range 2014)\ (range 1007)) disj_aux = 
        range 2014 := by 
        simp
      rw [←disu_aux, sum_disjUnion]
      have eq_aux : ∑ x_1 ∈ range 2014 \ range 1007, |x + ↑x_1 + 1|
        = ∑ k ∈ range 1007, |x + k + 1007 + 1| := by 
        let e : ℕ → ℕ := fun x => x + 1007
        apply Eq.symm
        apply Finset.sum_nbij' e (fun x => x - 1007)
        intro x hx 
        simp at hx
        unfold e
        simp
        linarith
        intro x hx 
        simp at hx
        simp
        obtain ⟨h1, h2⟩ := hx
        omega
        intro x hx
        unfold e
        omega
        intro x hx
        simp at hx
        unfold e
        omega
        intro y hy
        unfold e
        ring_nf
        have aux : 1008 + x + (y : ℝ) = 1 + x + ↑(1007 + y) := by 
          norm_num
          ring
        rw [aux]
      rw [eq_aux]
    rw [eq_aux]
    have eq_aux2 : 1007 ^  2 = ∑ i ∈ range 1007, (1007 : ℝ) := by 
      simp
      norm_num
    rw [eq_aux2]
    exact (sum_le_sum ineq_aux)
