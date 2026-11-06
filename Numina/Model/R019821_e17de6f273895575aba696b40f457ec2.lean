import Mathlib

theorem number_theory_11644 (x y z : ℕ) (hx : 1 ≤ x ∧ x ≤ 9) (hy : 0 ≤ y ∧ y ≤ 9) (hz : 0 ≤ z ∧ z ≤ 9)
    (h : 100 * x + 10 * y + z = Nat.factorial x + Nat.factorial y + Nat.factorial z) :
    x + y + z = 10 := by 
  have h1 : x ≤ 9 := by linarith [hx.right]
  have h2 : 1 ≤ x := by linarith [hx.left]
  have h3 : y ≤ 9 := by linarith [hy.right]
  have h4 : z ≤ 9 := by linarith [hz.right]
  interval_cases x <;> interval_cases y <;> interval_cases z <;> try { contradiction }
  <;> norm_num [Nat.factorial] at h ⊢ 
    <;> omega
  all_goals omega