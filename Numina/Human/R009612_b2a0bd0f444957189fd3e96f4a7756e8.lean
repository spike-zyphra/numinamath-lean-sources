import Mathlib

/- 10. (1994 Hebei Province High School Competition Question) Given the sequence $\left\{a_{n}\right\}(n=1,2, \cdots)$ where $a_{1}=1, a_{2}=3, a_{3}=6$, and for $n>3$, $a_{n}=3 a_{n-1}-a_{n-2}-2 a_{n-3}$.
Prove: For all natural numbers $n>3$, $a_{n}>3 \times 2^{n-2}$. -/
theorem algebra_284030 {a : ℕ → ℤ}
  (ha1 : a 1 = 1) (ha2 : a 2 = 3) (ha3 : a 3 = 6)
  (han : ∀ n > 3, a n = 3 * a (n - 1) - a (n - 2) - 2 * a (n - 3)) :
  ∀ n > 3, a n > 3 * 2 ^ (n - 2) := by
  -- let's show that for n>3 a_n > 2 * a_{n-1} using induction
  have h: ∀ n>3, a n > 2 * a (n-1) := by
    intro n hn
    induction' n using Nat.strong_induction_on with k ih
    -- we need to prove some low cases by hand
    match k with
    | 0 => linarith
    | 1 => linarith
    | 2 => linarith
    | 3 => linarith
    | 4 => simp; rw [han 4 (by norm_num), ha3]; simp; rw [ha2, ha1]; norm_num
    | 5 => simp; rw [han 5 (by norm_num), ha3]; simp; rw [han 4 (by norm_num)]; simp; rw [ha3, ha2, ha1]; norm_num
    | k+6 =>
      calc a (k+6)
      _ = 3 * a (k + 6-  1) - a (k + 6 - 2) - 2 * a (k + 6 - 3) := by rw [han (k+6) (by norm_num)]
      _ = 3 * a (k + 5) - a (k + 4) - 2 * a (k + 3) := by simp [Nat.add_sub_assoc]
      _ = 2 * a (k + 5) + a (k + 5) - a (k + 4) - 2 * a (k + 3) := by ring_nf
      _ > 2 * a (k + 5) + 2 * a (k + 5 - 1) - a (k + 4) - 2 * a (k + 3) := by linarith [ih (k+5) (by linarith) (by linarith)]
      _ = 2 * a (k + 5) + 2 * a (k + 4) - a (k + 4) - 2 * a (k + 3) := by simp
      _ = 2 * a (k + 5) + a (k + 4) - 2 * a (k + 3) := by ring_nf
      _ > 2 * a (k + 5) + 2 * a (k + 4 - 1) - 2 * a (k + 3) := by linarith [ih (k+4) (by linarith) (by linarith)]
      _ = 2 * a (k + 5) + 2 * a (k + 3) - 2 * a (k + 3) := by simp
      _ = 2 * a (k + 5) := by ring_nf
  -- now we can prove the main statement, again via (now more classical) induction
  intro n hn
  induction n, hn using Nat.le_induction
  case base => simp; rw [han 4 (by norm_num)]; simp; rw [ha3, ha2, ha1]; norm_num
  case succ n hn hmn =>
    calc a (n+1)
    _ > 2 * a (n+1-1) := by linarith [h (n+1) (by linarith)];
    _ = 2 * a n := by simp
    _ > 2 * (3 * 2 ^ (n - 2)) := by linarith [hmn]
    _ = 3 * 2 * 2 ^ (n - 2) := by ring_nf
    _ = 3 * 2 ^ (1 + (n - 2)) := by ring_nf
    _ = 3 * 2 ^ (n - 1) := by rw [← Nat.add_sub_assoc (by linarith), add_comm, ← Nat.sub_add_cancel  (n:=n) (m:=1) (by linarith)]; simp