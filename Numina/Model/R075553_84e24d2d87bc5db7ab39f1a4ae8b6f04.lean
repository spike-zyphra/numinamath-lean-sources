import Mathlib

theorem algebra_297446 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 3)
    (han : ∀ n, a (n + 2) = (n + 3) * a (n + 1) - (n + 2) * a n)
    (hdiv : ∀ m ≥ n, 9 ∣ a m) :
    n ≥ 5 := by
  by_contra h
  push_neg at h
  have h4 : n ≤ 4 := by 
    omega
  have h4' : 9 ∣ a 4 := hdiv 4 (by omega)
  -- First compute $a_3$ using recurrence relation
  have ha3 : a 3 = 9 := by
    specialize han 1
    norm_num at han
    rw [ha1, ha2] at han
    omega
  -- Then compute $a_4$ using recurrence relation and the value of $a_3$
  have ha4 : a 4 = 33 := by
    specialize han 2
    norm_num at han
    rw [ha2, ha3] at han
    omega
  rw [ha4] at h4'
  -- $9 \nmid 33$, contradiction
  norm_num at h4'
  all_goals omega
  all_goals omega