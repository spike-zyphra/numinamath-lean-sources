import Mathlib

open Real Set
open scoped BigOperators

/- 17. Given a quadrilateral whose vertices lie on the graph of the function $y=\ln x$, the x-coordinates of these vertices are four consecutive positive integers, and the area of the quadrilateral is $S=\ln \frac{91}{90}$. Then the x-coordinate of the leftmost vertex is ( ).
(A)6
(B) 7
(C) 10
(D) 12
(E) 13 -/

-- lemma to show inequality of logs that will be used for absolute value
lemma l_log_ineq (x : ℝ) (hx : 0 < x) : log x + log (x + 3) < log (x + 1) + log (x + 2) := by
  rw [← log_mul (by linarith) (by linarith), ← log_mul (by linarith) (by linarith)]
  apply strictMonoOn_log
  any_goals simp
  all_goals nlinarith

theorem calculus_237734 {n : ℕ} (hn : n > 0) (A B C D : ℝ × ℝ) (hA : A = (↑n, log n))
    (hB : B = (↑(n + 1), log (n + 1))) (hC : C = (↑(n + 2), log (n + 2))) (hD : D = (↑(n + 3), log (n + 3))) :
    (1/2 * |A.1 * B.2 - A.2 * B.1 + B.1 * C.2 - B.2 * C.1 + C.1 * D.2 - C.2 * D.1 + D.1 * A.2 - D.2 * A.1| =
    log (91 / 90)) ↔ n = 12 := by
  simp [hA, hB, hC, hD]
  constructor <;> rintro h
  -- proving n = 12, simplify expression an group all terms to one log in lhs, use lemma to take out absolute value
  . have h_log_ineq := l_log_ineq n (by norm_cast)
    ring_nf at h h_log_ineq
    rw [abs_eq_neg_self.mpr (by linarith)] at h
    ring_nf at h
    rw [← log_div (by linarith) (by positivity), ← log_div (by linarith) (by linarith), ← log_mul (by positivity) (by positivity)] at h
    -- due to injectivity, terms inside log are same
    replace h := Real.log_injOn_pos (by simp; positivity) (by simp) h
    -- cross multiply and get quadratic that is n = 12 or n = -15
    have : n * (3 + n : ℝ) ≠ 0 := by positivity
    field_simp at h
    ring_nf at h
    replace h : (n - 12 : ℝ) * (n + 15) = 0 := by linarith
    simp at h
    rw [sub_eq_zero, add_eq_zero_iff_eq_neg] at h
    -- n = 12 is only valid solution
    norm_cast at h
    simpa using h
  -- plug in n = 12, use lemma to get inequality to take out absolute value
  . rw [h]
    norm_cast
    ring_nf
    have h_log_ineq := l_log_ineq 12 (by norm_cast)
    ring_nf at h_log_ineq
    rw [abs_eq_neg_self.mpr (by linarith)]
    ring_nf
    -- merge all logs, the terms become same
    rw [← log_div (by norm_num) (by norm_num), ← log_div (by norm_num) (by norm_num), ← log_mul (by norm_num) (by norm_num)]
    ring_nf