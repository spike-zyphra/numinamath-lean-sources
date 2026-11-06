import Mathlib

open Real
open scoped BigOperators

/- 3.36 ** Let $a_{n}=1+\frac{1}{2}+\cdots+\frac{1}{n}$. Prove that when $n \geqslant 2$, we have

$$

a_{n}^{2}>2\left(\frac{a_{2}}{2}+\frac{a_{3}}{3}+\cdots+\frac{a_{n}}{n}\right) .

$$
 -/
theorem inequalities_267787 {a : ℕ → ℝ}
  (ha : ∀ n, a n = ∑ i in Finset.Icc 1 n, (1 : ℝ)/i) :
  ∀ n ≥ 2, (a n)^2 > 2 * ∑ i in Finset.Icc 2 n, a i / i := by
  -- since we'll go by induction, let's prove a stronger statement
  suffices ∀ n ≥ 2, (a n)^2 > 2 * ∑ i in Finset.Icc 2 n, a i / i + 1/n by
    intro n hn
    specialize this n hn;
    have hn:  1 / (n:ℝ) > 0 := by simp; linarith
    linarith
  intro n hn
  -- move from Icc to Ico for easier manipulation
  have hicc:∀ a b:ℕ, Finset.Icc a b = Finset.Ico a (b+1) := by
    intro a b
    ext c; simp; omega
  conv at ha => intro n; rhs; rw [hicc]
  rw [hicc]
  -- We'll also give a recursive relation for a n
  have ha2: ∀ n > 1, a n = a (n - 1) + 1 / n := by
    intro n hn
    rw [ha n, ha (n-1), Finset.sum_Ico_succ_top (by linarith)]
    have h:n - 1 + 1 = n := by omega
    simp [h]

  -- Then we can go with induction from n=2
  induction n, hn using Nat.le_induction
  case base =>
    simp; rw [ha 2, Finset.sum_Ico_eq_sum_range, Finset.sum_range_succ, Finset.sum_range_succ]; simp; ring_nf; norm_num
  case succ n' hmn hn =>
    calc a (n' + 1) ^ 2
    _ = (a n' + 1 / (n' + 1))^2 := by rw [ha2 (n'+1) (by linarith), Nat.add_sub_assoc, Nat.sub_self]; simp; norm_num
    _ = (a n')^2 + 2 * a n' * (1 / (n' + 1)) + (1 / (n' + 1))^2 := by ring_nf
    _ > 2 * ∑ i ∈ Finset.Ico 2 (n' + 1), a i / ↑i   + 1 / ↑n' + 2 * a n' * (1 / (n' + 1)) + (1 / (n' + 1))^2 := by linarith [hn];
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 1), a i / i)    + 1 / ↑n' + 2 * (a (n'+1) - 1 / (n'+1)) * (1 / (n' + 1)) + (1 / (n' + 1))^2 := by simp; left; rw [ha2 (n'+1) (by linarith)]; simp
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 1), a i / i)    + (1 / ↑n' + 2 * (a (n'+1) - 1 / (n'+1)) * (1 / (n' + 1)) + (1 / (n' + 1))^2) := by rw [← add_assoc, ← add_assoc];
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 1), a i / i)    + ( 2*a (n'+1)/(n'+1) + 1/n' - 1/(n'+1)^2) := by simp; ring_nf; rw [add_assoc]; simp; rw [sub_add]; simp; ring_nf
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 1), a i / i) +  2*a (n'+1)/(n'+1) + (1/n' - 1/(n'+1)^2) := by rw [add_assoc]; simp; ring_nf
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + (1/n' - 1/(n'+1)^2) := by simp; rw [Finset.sum_Ico_succ_top (b:=n'+1) (by linarith), mul_add, mul_div_assoc]; norm_cast
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + (1/n'*((n'+1)^2/(n'+1)^2) - 1/(n'+1)^2 * (n'/n')) := by rw [div_self (by simp; linarith), div_self (by simp; linarith)]; simp;
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + (n'^2+n'+1)/(n'*(n'+1)^2) := by rw [add_right_inj (2 * ∑ i ∈ Finset.Ico 2 (n' + 2), a i / ↑i ), div_mul_div_comm, div_mul_div_comm, one_mul]; ring_nf
    _ > 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + (n'^2+n')/(n'*(n'+1)^2) := by simp; apply div_lt_div_of_pos_right (by simp); apply mul_pos; simp; linarith; norm_cast; simp
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + (n'^2+n')/((n'^2+n')*(n'+1)) := by simp; ring_nf
    _ = 2 * (∑ i ∈ Finset.Ico 2 (n' + 2), a i / i) + 1/(n'+1) := by simp; rw [← div_div, div_self (by simp; apply ne_of_gt; apply add_pos; norm_cast; nlinarith; norm_cast; nlinarith)]; ring_nf
    _ = 2 * ∑ i ∈ Finset.Ico 2 (n' + 1 + 1), a i / ↑i + 1 / ↑(n' + 1) := by simp