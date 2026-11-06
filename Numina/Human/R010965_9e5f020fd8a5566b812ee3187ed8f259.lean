import Mathlib

open Polynomial

namespace algebra_210421

/- Given coprime integers `a` and `b` (`h : IsCoprime a b`) and an equality
`a * x = b * y`, this theorem produces an integer `k : ℤ` such that
`x = b * k` and `y = a * k`. -/
theorem exists_eq_mul_and_eq_mul_of_mul_eq_mul
    {a b x y : ℤ} (h : IsCoprime a b) (hxy : a * x = b * y) :
    ∃ k : ℤ, x = b * k ∧ y = a * k := by
  by_cases hb : b = 0
  · subst hb
    rw [isCoprime_zero_right] at h
    obtain rfl | rfl := Int.isUnit_eq_one_or h
    · simpa using hxy
    · use - 1 * y
      simpa using hxy
  · have h1 : b ∣ a * x := by simp [hxy]
    have h2 : b ∣ x :=
      IsCoprime.dvd_of_dvd_mul_left (IsCoprime.symm h) h1
    obtain ⟨k, rfl⟩ := h2
    use k
    simp only [true_and]
    apply mul_left_cancel₀ hb
    rw [← hxy]
    ring

end algebra_210421

open algebra_210421

/- Auto: : Agakhanov N. $\mathbf{H}$.
Find the free term of the polynomial $P(x)$ with integer coefficients,
if it is known that it is less than a thousand in absolute value, and $P(19)=P(94)=1994$.-/
theorem algebra_210421 {P : ℤ[X]} (hP0 : |coeff P 0| < 1000)
    (hP : eval 19 P = 1994 ∧ eval 94 P = 1994) : coeff P 0 = 208 := by
  -- Let $a_0$ be the constant term of $P(x)$. We can write
  -- $$ P(x) = xQ(x) + a_0, $$ where $Q(x)$ is an integer‐coefficient polynomial.
  let Q := Polynomial.divX P
  have hQ : X * Q + C (coeff P 0) = P := (X_mul_divX_add P)
  -- Hence
  -- $$ P(19) = 19n + a_0,\quad P(94) = 94m + a_0, $$
  -- for some integers $n$ and $m$.
  rw [← hQ] at hP
  simp only [eq_intCast, eval_add, eval_mul, eval_X, eval_intCast, Int.cast_id] at hP
  rcases hP with ⟨hP1, hP2⟩
  set m := eval 19 Q with hm 
  set n := eval 94 Q with hn 
  -- Since $P(19)=P(94)$, we have
  -- $$ 19n = 94m \Longrightarrow n = 94k,; m = 19k $$
  -- for some integer $k$
  have eq1 : 19 * m = 94 * n := by
    apply add_right_cancel (b := coeff P 0)
    rw [hP1, hP2]
  have eq2 : ∃ k : ℤ, m = 94 * k ∧ n = 19 * k :=
    exists_eq_mul_and_eq_mul_of_mul_eq_mul (by norm_num) eq1
  -- Substituting back gives
  -- $$ 19\cdot 94k + a_0 = 1994 \Longrightarrow  a_0 = 1994 - 1786k. $$
  obtain ⟨k, hmk, hnk⟩ := eq2
  simp only [hn, hnk] at hP2
  ring_nf at hP2
  rw [abs_lt] at hP0
  -- The condition $\lvert a_0\rvert &lt; 1000$ forces $k=1$, so
  -- $$ a_0 = 1994 - 1786 = 208.$$
  have hk : k = 1 := by
    by_cases hk : 2 ≤ |k|
    · rw [le_abs'] at hk
      absurd hP0
      rcases hk with hk1 | hk2
      <;> linarith
    · simp only [le_abs, not_or, not_le, n] at hk
      rcases hk with ⟨hk1, hk2⟩
      replace hk1 : k ≤ 1 := by linarith only [hk1]
      replace hk2 : k ≥ -1 := by linarith only [hk2]
      interval_cases k
      · absurd hP0
        linarith
      · absurd hP0
        linarith
      · rfl
  subst hk 
  rw [← hn, hnk] at hP2
  apply add_left_cancel (a := 19 * 1 * 94)
  rw [hP2]
  norm_num
