import Mathlib.Tactic

/-
PROBLEM:
John is walking east at a speed of 3 miles per hour, while Bob is also walking east, but at a speed of 5 miles per hour.  If Bob is now 1 mile west of John, how many minutes will it take for Bob to catch up to John?
$\text {(A) } 30 \qquad \text {(B) } 50 \qquad \text {(C) } 60 \qquad \text {(D) } 90 \qquad \text {(E) } 120$
-/

theorem alg_1175
  (j b c d h : ℚ)
  (john_speed : j = 3)
  (bob_speed : b = 5)
  (catchup_speed_bob : c = b - j)
  (distance_between_them : d = 1)
  (hour_needed : h = d / c) :
  h = 1/2 := by
    rw [john_speed, bob_speed] at catchup_speed_bob
    norm_num at catchup_speed_bob
    rw [catchup_speed_bob, distance_between_them] at hour_needed
    exact hour_needed