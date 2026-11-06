import Mathlib

theorem algebra_265615 (a b : Finset ℝ)
    (ha : a.card = 10 ∧ ∑ x ∈ a, x = 41.8 * 10 + 44)
    (hb : b.card = 10 ∧ ∑ x ∈ b, x = 41.8 * 10 + 44 + 47) :
    (41.8 * 10 + 44 + 47) / 12 > 42.2 := by 
  norm_num
  <;> try { native_decide }
  all_goals try norm_num
  <;> try { native_decide }
  all_goals try norm_num
  <;> try { native_decide }
  all_goals try norm_num
  <;> try { native_decide }
  all_goals try norm_num
  <;> try { native_decide }
  all_goals try norm_num
  <;> try { native_decide }
  all_goals try nlinarith
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> try { native_decide }
  <;> norm_num
  <;> try { native_decide }