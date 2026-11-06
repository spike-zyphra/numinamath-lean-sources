import Mathlib

/- 6. If the sequence $\left\{a_{n}\right\}$ satisfies
$$
a_{n+1}=\left\{\begin{array}{ll}
2 a_{n}, & 0 \leqslant a_{n}<\frac{1}{2} ; \\
2 a_{n}-1, & \frac{1}{2} \leqslant a_{n}<1 .
\end{array}\right.
$$

If $a_{1}=\frac{6}{7}$, then $a_{23}=$
A. $\frac{6}{7}$
B. $\frac{5}{7}$
C. $\frac{3}{7}$
D. 0 -/
theorem algebra_197414 (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n ∧ a n < 1 / 2 → a (n + 1) = 2 * a n)
    (ha' : ∀ n, 1 / 2 ≤ a n ∧ a n < 1 → a (n + 1) = 2 * a n - 1) (ha'' : a 1 = 6 / 7) :
    a 23 = 5 / 7 := by
    
    -- We prove the following lemma on the value of a k by induction, using the hypothesis.
    have lem: ∀ k : ℕ, ((k+1) % 3 = 1 → a (k+1) = 6/7) ∧ ((k+1) % 3 = 2 → a (k+1) = 5/7) ∧ ((k+1) % 3 = 0 → a (k+1) = 3/7) := by 
      intro k
      induction' k with k hk
      simp; assumption

      by_cases kp1p1m3e1 : (k+1+1) %3 =1
      simp [kp1p1m3e1]
      have kp1m3e0 : (k+1) %3 = 0 := by omega
      apply hk.right.right at kp1m3e0
      have bb: 0 ≤ a (k+1) ∧ a (k+1) < 1/2 := by rw [kp1m3e0]; norm_num
      have : a (k+1+1) = 2 * a (k+1) := by apply ha (k+1); assumption
      rw [kp1m3e0] at this; ring_nf at this; ring_nf; assumption

      by_cases kp1p1m3e2 : (k+1+1) %3 =2
      simp [kp1p1m3e2]
      have kp1m3e1 : (k+1) %3 = 1 := by omega
      apply hk.left at kp1m3e1
      have bb: 1/2 ≤ a (k+1) ∧ a (k+1) < 1 := by rw [kp1m3e1]; norm_num
      have : a (k+1+1) = 2 * a (k+1) - 1 := by apply ha' (k+1); assumption
      rw [kp1m3e1] at this; ring_nf at this; ring_nf; assumption

      have kp1p1m3e0 : (k+1+1) %3 =0 := by omega
      simp [kp1p1m3e0]
      have kp1m3e2 : (k+1) %3 = 2 := by omega
      apply hk.right.left at kp1m3e2
      have bb: 1/2 ≤ a (k+1) ∧ a (k+1) < 1 := by rw [kp1m3e2]; norm_num
      have : a (k+1+1) = 2 * a (k+1)-1 := by apply ha' (k+1); assumption
      rw [kp1m3e2] at this; ring_nf at this; ring_nf; assumption

    -- Now just apply the induction and get the value of a 23.
    have cla : ((22 + 1) % 3 = 1 → a (22 + 1) = 6 / 7) ∧ ((22 + 1) % 3 = 2 → a (22 + 1) = 5 / 7) ∧ ((22 + 1) % 3 = 0 → a (22 + 1) = 3 / 7) := by apply lem 22
    have cla2 : ((22 + 1) % 3 = 2 → a (22 + 1) = 5 / 7) := by exact cla.right.left
    have t : (22+1)%3 = 2 := by norm_num
    apply cla2 at t; simp at t; assumption