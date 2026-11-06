import Mathlib

set_option maxHeartbeats 1000000

-- 3. A number consists of only two digits: 3 or 4, and both 3 and 4 must appear at least once. This number is a multiple of both 3 and 4. The smallest such number is $\qquad$ .

-- 【答案】 3444

-- 【解答】为了使得它是 4 的倍数, 最后两位只能是 44 。如果只有两个数字 4 , 这个数无法成为 3 的倍数，所以很容易得到其最小值为 3444

theorem number_theory_134288 :
  IsLeast {n : ℕ | (∀ d ∈ Nat.digits 10 n, d = 3 ∨ d = 4) ∧ 3 ∈ Nat.digits 10 n ∧ 4 ∈ Nat.digits 10 n ∧ 3 ∣ n ∧ 4 ∣ n} 3444 := by

  refine ⟨by simp; constructor; all_goals omega, ?_⟩
  unfold lowerBounds
  simp
  intro n hn h3 h4 h_dvd3 h_dvd4

  by_contra h
  simp at h
  let m := n / 12
  have hm : n = m * 12 := by
    have h12 : 12 ∣ n := by
      rw [Nat.dvd_iff_mod_eq_zero] at h_dvd3 h_dvd4 ⊢
      omega
    rw [← Nat.mul_div_cancel' h12]
    ring
  have : m < 287 := by
    rw [hm] at h
    linarith

  interval_cases m
  all_goals
  . norm_num at hm
    subst n
    try simp at hn h3 h4
