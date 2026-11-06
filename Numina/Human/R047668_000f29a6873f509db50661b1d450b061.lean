import Mathlib

/- $3 \cdot 44$ To complete the same work, the time required for $A$ to work alone is $m$ times the time required for $B$ and $C$ to work together; the time required for $B$ to work alone is $n$ times the time required for $A$ and $C$ to work together; and the time required for $C$ to work alone is $k$ times the time required for $A$ and $B$ to work together; then $k$ expressed in terms of $m, n$ is
(A) $\frac{2 m n}{m+n}$.
(B) $\frac{1}{m+n-m n}$.
(C) $\frac{1-m n}{m+n+2 m n}$.
(D) $\frac{m+n+2}{m n-1}$.
(2nd "Jinyun Cup" Junior High School Mathematics Invitational Competition, 1985) -/
theorem algebra_210959 {a b c m n k : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hm : 0 < m) (hn : 0 < n) (hk : 0 < k)
    (h1 : 1 / a = m / (b + c)) (h2 : 1 / b = n /(a + c))
    (h3 : 1 / c = k / (a + b)) :
    k = (m + n + 2) / (m * n - 1) := by
  -- a = work done by A per unit time
  -- b = work done by B per unit time
  -- c = work done by C per unit time
  -- when you have x work done per unit time, then it takes 1/x unit of time to do full work
  field_simp at h1; ring_nf at h1
  field_simp at h2; ring_nf at h2
  field_simp at h3
  -- first eliminate b
  have : b = m * a - c := by linarith
  subst this
  -- next express a in terms of others, to do this, prove 1-nm ≠ 0 as it being 0 implies c * (n + 1) = 0 => c = 0, impossible
  have : a * (1 - n * m) = -n * c - c := by linarith
  have hnm : 1 - n * m ≠ 0 := by
    by_contra hnm
    have : n * m = 1 := by linarith
    ring_nf at h2; rw [mul_assoc, this] at h2
    have : c * (n + 1) = 0 := by linarith
    field_simp at this
  have : a = ( -n * c - c) / (1 - n * m) := by
    field_simp
    linarith
  subst this
  clear * - this hc hm hn hnm hk h3
  -- finally in 3rd equation eliminate c as it is factored out from both sides
  field_simp at h3
  have hk' : c * (-n - 2 - m) = c * (-n*m*k + k) := by linarith
  simp [show c ≠ 0 by positivity] at hk'
  -- finally multiply and show algebraically the formula for k
  ring_nf
  have := neg_ne_zero.mpr hnm
  have : -1 + m * n ≠ 0 := by convert this using 1; ring
  field_simp
  linarith