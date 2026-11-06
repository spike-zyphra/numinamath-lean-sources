import Mathlib

theorem number_theory_130647 (y : ℕ) (hy : y < 1953) (h : (1953 - y) % 9 = 0) (h' : (1953 - y) = (Nat.digits 10 y).sum) :
    (1953 - y) = 18 := by
  interval_cases y <;> norm_num at h h' ⊢ <;> all_goals
    try { try { trivial } }
    <;> try { contradiction }
    <;> try { omega }
    <;> try { linarith }
    <;> try { native_decide }