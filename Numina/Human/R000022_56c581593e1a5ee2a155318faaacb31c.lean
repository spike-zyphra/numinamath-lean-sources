import Mathlib

/-- Define `fa n af` as a polynomial with integer coefficients, and coefficients are decided by the parameter `af`. -/
def fa(n:ℕ)(af :ℕ → ℤ)(x: ℤ): ℤ :=
 (∑ i in Finset.range (n), (af i) * x^i)

/-- Auxiliary lemma : if $P$ is a integer polynomial and $x,y$ are integers, 
    then $x-y \mid (P(x) - p(y))$.  -/
lemma subLemma(af :ℕ → ℤ)(x y:ℤ)(n:ℕ): (x-y)∣ ((fa n af x) - (fa n af y)):= by
unfold fa
cases n with
| zero => simp
| succ n => simp [Finset.sum_range_succ]
            have h0:∑ i ∈ Finset.range n, af i * x ^ i + af n * x ^ n - (∑ i ∈ Finset.range n, af i * y ^ i + af n * y ^ n) =( ∑ i ∈ Finset.range n, af i * x ^ i- (∑ i ∈ Finset.range n, af i * y ^ i )) + (af n * x ^ n - af n * y ^ n):= by ring
            rw[h0]
            apply dvd_add
            have ht:= subLemma af x y n
            exact ht
            have h1:af n * x ^ n - af n * y ^ n = af n * (x ^ n - y ^ n):= by ring
            rw [h1]
            have h2:=Polynomial.powSubPowFactor x y n
            obtain ⟨m, hm⟩ := h2
            rw [hm]
            rw [mul_comm,mul_comm m]
            rw [mul_assoc]
            simp



/-- Let $\(a, b, c\)$ be distinct integers. Show that there does not exist a polynomial $\(P\)$ with integer coefficients such that $\(P(a)=b\)$, $\(P(b)=c\)$, and $\(P(c)=a\)$.-/
theorem algebra_4034
(n:ℕ)(a b c:ℤ )(af :ℕ → ℤ)(ha: fa n af a = b)(hb: fa n af b = c)(hc: fa n af c = a)
(hab: a ≠ b)(hbc: b ≠ c)(hac: a ≠ c):False:= by
-- we get `a - b ∣ fa n af a - fa n af b`, ` b - c ∣ fa n af b - fa n af c` and 
-- `c - a ∣ fa n af c - fa n af a` by above lemma.
have h1:= subLemma af a b n
have h2:= subLemma af b c n
have h3:= subLemma af c a n
-- replace `fa n af a `, `fa n af b ` and `fa n af c `
rw [ha,hb] at h1
rw [hb,hc] at h2
rw [hc,ha] at h3
obtain ⟨m, hm⟩ := h1
obtain ⟨m1, hm1⟩ := h2
obtain ⟨m2, hm2⟩ := h3
have h4: (a-b)*(b-c)*(c-a)=(a-b)*(b-c)*(c-a) := rfl
nth_rw 1 [hm] at h4
nth_rw 1 [hm1] at h4
nth_rw 1 [hm2] at h4
-- replace $a-b, b-c, c-a$ by $(c-a)*m2, (a-b)*m, (b-c)*m1$ and simplify we get 
-- $((a - b) * (b - c) * (c - a))*1 = ((a - b) * (b - c) * (c - a))*(m*m1*m2)$.
have h5:((a - b) * (b - c) * (c - a))*1 = ((a - b) * (b - c) * (c - a))*(m*m1*m2):= by linarith
have h6: ((a - b) * (b - c) * (c - a)) ≠ 0 := by
  apply mul_ne_zero
  apply mul_ne_zero
  intro h
  have : a = b := by linarith
  contradiction
  intro h
  have : b = c := by linarith
  contradiction
  intro h
  have : a = c := by linarith
  contradiction
have h7: m*m1*m2=1:= by exact Eq.symm ((fun {a b c} h ↦ (Int.mul_eq_mul_left_iff h).mp) h6 h5)
have h8:=  Int.mul_eq_one_iff_eq_one_or_neg_one.mp h7
cases h8
rename_i h9
rw [h9.2] at hm2
rw [hm2] at hm
have h10:= Int.mul_eq_one_iff_eq_one_or_neg_one.mp h9.1
cases h10
rename_i h11
rw [h11.1] at hm
rw [h11.2] at hm1
simp_all
have h:b=c:= by linarith
contradiction

rename_i h11
rw [h11.1] at hm
rw [h11.2] at hm1
have h:b=c:= by linarith
contradiction


rename_i h11
rw [h11.2] at hm2
have h:b=c:= by linarith
contradiction
