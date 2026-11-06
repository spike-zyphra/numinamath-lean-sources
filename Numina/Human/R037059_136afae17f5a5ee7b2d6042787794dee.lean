import Mathlib

/-In the forest, there grew pines, cedars, and larches, and there were cones on all the trees, and they were equal in number. 
A gentle breeze blew, and several cones fell to the ground. It turned out that 11% of the cones fell from each pine, 
54% from each cedar, and 97% from each larch. At the same time, exactly 30% of all the cones hanging on the trees fell
 from all the trees together. Prove that the total number of trees in the forest is divisible by 43.-/
theorem number_theory_289107 (n m l : ℕ) 
(h3 : (11 / 100 : ℝ) * n + (54 / 100 : ℝ) * m + (97 / 100 : ℝ) * l = 30 / 100 * (n + m + l)): 43 ∣ n + m + l := by
  -- simplify the expression
  have eq2 : (19 : ℝ) * n = (24 : ℝ) * m + (67 : ℝ) * l := by
    linarith [h3]
  -- cast into ℕ
  have h7 : 19 * n = 24 * m + 67 * l := by
    have h_eq : (19 : ℝ) * (n : ℝ) = (24 : ℝ) * (m : ℝ) + (67 : ℝ) * (l : ℝ) := by
      linarith [h3]
    have h20 : (19 * n : ℝ) = (24 * m + 67 * l : ℝ) := by
      linarith [h3] 
    exact_mod_cast h20
  clear eq2 h3
  omega