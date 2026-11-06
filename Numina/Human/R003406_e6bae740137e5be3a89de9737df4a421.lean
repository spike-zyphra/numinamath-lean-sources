import Mathlib

/- ## Task 3 - 090933

For a certain task, A needs exactly m times as long as B and C together; B needs exactly n times as long as C and A together, and C exactly p times as long as A and B together. Calculate $p$ in terms of $m$ and $n$! -/
theorem algebra_177224 {a b c m n p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (mpos : m > 0) (npos : n > 0) (ppos : p > 0)
    (h1 : a = m * (b + c)) (h2 : b = n * (c + a)) (h3 : c = p * (a + b)) :
    p = (1 - m * n) / (2 * m * n + m + n) := by 
  --have n ≠ 0 by by definition of "n-times more"
  have hn : n ≠ 0 := by
    by_contra h
    rw[h] at h2
    norm_num at h2
    linarith
  --have m ≠ 0 by by definition of "m-times more"
  have hm : m ≠ 0 := by
    by_contra h
    rw[h] at h1
    norm_num at h1
    linarith
  --rewrite the first condition to find b
  have hb' : b = a / m - c := by 
    ring_nf at h1 
    field_simp
    linarith 
  --write b in the second equation
  rw[hb'] at h2
  --m * n ≠ 1 because if it where, then it would force c = 0 or m = -1
  have : 1 - m * n ≠ 0 := by
    by_contra kk
    have : n = 1 / m := by field_simp; linarith
    rw[this] at h2
    field_simp at h2
    have contr : c * (1 + m) = 0 := by linarith
    rw[mul_eq_zero] at contr
    obtain contr1|contr2 := contr
    · linarith
    · linarith
  --one can then find a in the second equation in terms of c
  have ha' : a = (n + 1) / (1 / m - n) * c := by
    field_simp at h2 ⊢
    ring_nf at h2 ⊢
    linarith
  --rewrite a in the third equation
  rw[h3] at hb'
  --from a in terms of c and b in terms of a and c, one can also find a + b in terms of c 
  have hadd : a + b = a * (1 + 1 / m) - c := by 
    field_simp at ha' ⊢
    linarith
  --rewrite it in h3 and rewrite a in function of c to find an expression containing c, p, m and n
  rw[hadd] at h3
  have eq : c * (1 + p) = p * a * (1 + 1 / m) := by 
    field_simp at h3 ⊢
    linarith
  rw[ha', ← mul_assoc] at eq
  rw[mul_comm (p * ((n + 1) / (1 / m - n))) c] at eq
  rw[mul_assoc] at eq
  --simplify ⬝c on both sides of the equation
  have eq' := congrFun (congrArg HMul.hMul eq) (1/c)
  rw[mul_assoc, mul_comm (1 + p) (1 / c), ← mul_assoc, ← mul_div_assoc, mul_one, div_self (by linarith)] at eq'
  rw[mul_assoc, mul_comm (p * ((n + 1) / (1 / m - n)) * (1 + 1 / m)) (1 / c), ← mul_assoc, ← mul_div_assoc, mul_one, div_self (by linarith)] at eq'
  --an equation in terms of p m n is left and it suffices to solve it in terms of p to find the result, one can do so with standard linear arithmetic
  rw[(by field_simp; ring_nf : p * ((n + 1) / (1 / m - n)) * (1 + 1 / m) = p * ((n + 1)*(m + 1)) / (1 - m * n))] at eq'
  field_simp at eq'
  have final_eq : 1 - m * n = p * ((n + 1) * (m + 1) - (1 - m * n)) := by ring_nf at eq ⊢; linarith
  field_simp
  ring_nf at final_eq ⊢
  linarith