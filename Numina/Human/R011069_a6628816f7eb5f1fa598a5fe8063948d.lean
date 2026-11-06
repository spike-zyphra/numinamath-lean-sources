import Mathlib

/- Example 9 Given positive integers $a_{0}, a_{1}, \cdots, a_{100}$, it is known that $a_{1}>a_{0}, a_{2}=3 a_{1}-2 a_{0}, a_{3}=3 a_{2}-2 a_{1}$, $\cdots, a_{100}=3 a_{99}-2 a_{98}$. Prove: $a_{100}>2^{99}$.
(2nd All-Russian Olympiad Problem) -/
theorem number_theory_120642 (a : ℕ → ℤ) (ha : ∀ n, 0 < a n)
    (h1 : a 0 < a 1) (hn : ∀(n:ℕ), 1<n → a n = 3 * a (n-1) - 2 * a (n-2)) :
    2 ^ 99 < a 100 := by
  -- We define: x = a_0, y = a_1 - a_0
  let x := a 0
  let y := a 1 - a 0
  -- Then by induction, we prove that a_n = x + y*(2^n -1):
  have (n:ℕ): a n = x + y * (2^n - 1) := by
    induction n using Nat.strong_induction_on
    case h n h_ind =>
      by_cases h: 1 < n
      case pos =>
        calc a n
            = 3 * a (n-1) - 2 * a (n-2) := by rw [hn]; assumption
          _ = a (n-1) + 2* (a (n-1) - a (n-2)) := by ring
          _ = x + y * (2^(n-1) - 1) + 2 * (x + y * (2^(n-1) - 1) - (x + y * (2^(n-2) - 1))) := by rw [h_ind, h_ind] <;> omega
          _ = x + y * (2^(n-1) - 1) + 2 * y * (2^(n-1) - 2^(n-2)) := by ring
          _ = x + y * (2^(n-1) - 1 + 2 * (2^(n-1) - 2^(n-2))) := by ring
          _ = x + y * (2^(n-1) + 2 * 2^(n-1) - 2 * 2^(n-2) - 1) := by ring
          _ = x + y * (2^(n-1) + 2^n - 2^(n-1) - 1) := by
            rw [← pow_succ', ← pow_succ']
            rw [← Nat.sub_add_comm (by linarith), ← Nat.sub_add_comm (by linarith)]
            simp
          _ = _ := by ring
      case neg =>
        interval_cases n
        case «0» => simp
        case «1» => unfold x y; simp
  -- Since x,y are both positive, we get a_100 = x + y*(2^100 - 1) ≥ 2^100 > 2^99
  have hx : 0 < x := by unfold x; apply ha
  have hy : 0 < y := by unfold y; linarith
  calc a 100 = x + y * (2^100 - 1) := by apply this
    _ ≥ 2^100 := by linarith
    _ > 2^99 := by norm_num