import Mathlib

theorem algebra_15882 {n m p : ℝ} (hnm : 5 / 6 = n / 72) (hmp : n / 72 = (m + n) / 84)
    (hmp' : (m + n) / 84 = (p - m) / 120) :
    p = 110 := by
  have hn : n = 60 := by
    linarith
  have hm : m = 10 := by
    rw [hn] at hmp
    linarith
  have hp : p = 110 := by
    have h1 : m + n = 70 := by
      linarith [hn, hm]
    have h2 : (m + n) / 84 = (p - m) / 120 := by
      linarith [hmp']
    rw [h1] at h2
    rw [hm] at h2
    linarith
  exact hp