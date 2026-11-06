import Mathlib

/-Find the positive integers $n$ with $n \geq 4$ such that $[\sqrt{n}]+1$ divides $n-1$ and $[\sqrt{n}]-1$ divides $n+1$.-/
theorem number_theory_90468 (nge : 4 ≤ n) : n.sqrt + 1 ∣ n - 1 ∧
    n.sqrt - 1 ∣ n + 1 ↔ n = 4 ∨ n = 7 ∨ n = 9 ∨ n = 13 ∨ n = 31 := by
-- Denote $n.sqrt$ by $a$ and $n-a^2$ by $r$
  set a := n.sqrt with ha; let r := n - a ^ 2
  have age : 2 ≤ a := by
    dsimp [a]; rw [Nat.le_sqrt]; omega
  have : 2 ^ 2 ≤ a ^ 2 := by gcongr
  rw [Nat.eq_sqrt, ← pow_two, ← pow_two] at ha
  have rlt : r < 2 * a + 1 := by
    norm_num [add_sq] at ha; omega
  have hn : n = a ^ 2 + r := by omega
  constructor
  -- Rewrite and simplify the two division relations `dvd1` and `dvd2`
  · rintro ⟨dvd1, dvd2⟩
    rw [hn, Nat.sub_add_comm] at dvd1
    nth_rw 2 [show 1 = 1^2 by rfl] at dvd1
    rw [hn, show a^2+r+1 = a^2-1^2+(r+2) by omega] at dvd2
    rw [Nat.sq_sub_sq, ← Nat.dvd_add_iff_right] at dvd1 dvd2
  -- If $r=0$, we can get $a=2$ or $a=3$, then $n=4$ or $n=9$
    by_cases h : r = 0
    · simp [h] at *
      apply Nat.le_of_dvd at dvd2
      replace dvd2 : a ≤ 3 := by omega
      interval_cases a; all_goals simp [hn]
  -- If $r≠0$, we can prove that $r=a+1$ and $a-1$ divides $4$
    rcases dvd1 with ⟨k, hk⟩
    have kpos : 0 < k := by
      by_contra!; simp at this
      simp [this] at hk; omega
    have klt : k < 2 := by
      by_contra!; rw [hk] at rlt
      convert rlt; simp; calc
        _ < (a + 1) * 2 := by omega
        _ ≤ _ := by gcongr
    replace klt : k = 1 := by omega
    simp [klt] at hk; rw [hk] at dvd2
    rw [show a+1+2 = a-1+4 by omega, ← Nat.dvd_add_iff_right] at dvd2
  -- Therefore $a$ is at most $5$, we can discuss all possible values of $a$ to find the rest solutions
    have : a ≤ 5 := by
      apply Nat.le_of_dvd at dvd2
      all_goals omega
    interval_cases a; any_goals omega
    all_goals simp
-- Conversely, it is straightforward to check that the given values are solutions to the equation
  intro h; rcases h with h|h|h|h|h
  all_goals norm_num [h, a]