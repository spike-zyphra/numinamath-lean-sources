import Mathlib

theorem algebra_15714 : (({(3, 10), (6, 20), (12, 35), (18, 40), (20, 50)} : Finset (ℝ × ℝ)).filter (fun (x, y) => y > 2 * x + 7)).sum (fun (x, y) => x) = 38 := by 
  norm_num [Finset.sum_filter]
  <;> try { simp }
  <;> try { norm_num }