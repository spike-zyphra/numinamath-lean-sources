import Mathlib

open Finset

theorem number_theory_195366 {x:ℤ} {s1 s2: Finset ℤ}
  (sumeq: ∑ i ∈ (Icc 0 85), (x + i) = 2021)
  (hs1: s1 = Finset.filter (x + · > (0:ℤ)) (Icc 0 85))
  (hs2: s2 = Finset.filter (x + · < (0:ℤ)) (Icc 0 85)):
  (∑ i ∈ s1, (x+i))/(s1.card:ℝ) - (∑ i ∈ s2, (x+i))/(s2.card:ℝ) = 43.5 := by

  have h1 : x = -19 := by
    have h6 : ∑ i in Icc (0 : ℤ) (85 : ℤ), (x + i) = 86 * x + 3655 := by 
      have h51 : ∑ i in Icc (0 : ℤ) (85 : ℤ), (x + i) = ∑ i in Icc (0 : ℤ) (85 : ℤ), (x : ℤ) + ∑ i in Icc (0 : ℤ) (85 : ℤ), (i : ℤ) := by 
        rw [Finset.sum_add_distrib]
      have h52 : ∑ i in Icc (0 : ℤ) (85 : ℤ), (x : ℤ) = 86 * x := by
        simp [Finset.sum_const, Finset.card_range]
      have h53 : ∑ i in Icc (0 : ℤ) (85 : ℤ), (i : ℤ) = 3655 := by 
        native_decide
      rw [h51]
      rw [h52, h53]
    linarith [h6, sumeq]

  have HX : x = -19 := h1

  have h2 : s1 = filter (fun i => -19 + i > (0 : ℤ)) (Icc 0 85) := by 
    rw [hs1]
    simp [show x = -19 by linarith [h1]]
  have h3 : s2 = filter (fun i => -19 + i < (0 : ℤ)) (Icc 0 85) := by 
    rw [hs2]
    simp [show x = -19 by linarith [h1]]
  -- The summation parts 
  have h4 : ∑ i in s1, (x + i) = 2211 := by 
    rw [h2, show x = -19 by linarith [h1]]
    native_decide 
  have h5 : ∑ i in s2, (x + i) = -190 := by 
    rw [h3, show x = -19 by linarith [h1]]
    native_decide
  -- Now, cardinality of s1 and s2 
  have h71 : s1.card = 66 := by
    rw [h2]
    native_decide 
  have h72 : s2.card = 19 := by 
    rw [h3]
    native_decide
  have h7 : (s1.card : ℝ) = (66 : ℝ) := by 
    have h8 : (s1.card : ℝ) = (66 : ℝ) := by 
      have h9 : s1.card = 66 := by
        exact h71
      exact_mod_cast h9 
    linarith 
  have h6 : (s2.card : ℝ) = (19 : ℝ) := by 
    have h8 : (s2.card : ℝ) = (19 : ℝ) := by 
      have h9 : s2.card = 19 := by 
        exact h72 
      exact_mod_cast h9 
    linarith 
  -- The summation parts and cardinalities have been computed. Now compute the final result.
  rw [h4, h5, h7, h6]
  all_goals norm_num