import Mathlib

/- An infinite geometric series has sum 2000.  A new series, obtained by squaring each term of the original series, has sum 16 times the sum of the original series.  The common ratio of the original series is $m/n$, where $m$ and $n$ are relatively prime positive integers. Find $m+n$.-/

theorem algebra_19139 {a r : ℚ} (f : ℕ → ℚ )(hr : r < 1 ) (hr1 : 0 < r) (h : ∑' n : ℕ, ((r ^ n) : ℝ) * a = 2000)

    (h' : ∑' n : ℕ,  (((r ^ 2) ^ n) : ℝ)* a ^ 2 = 16 * 2000) :

    r.num +r.den = 125 := by
    --Let $a$ be the first term and $r$ the ratio of the original series, and let $S=2000$.  Then $\displaystyle{a\over{1-r}}=S$ and $\displaystyle{{a^2}\over{1-r^2}}=16S$. Factor to obtain $16S=\displaystyle\left({a\over{1-r}}\right)
    have  hr2 : 0 ≤ r := by linarith
    rw [Summable.tsum_mul_right] at h
    have heq :   (∑' (i : ℕ), (r : ℝ) ^ i) = (1 - (r : ℝ))⁻¹   := by
      apply tsum_geometric_of_lt_one
      norm_cast
      norm_cast
    rw[heq] at h
    rw [Summable.tsum_mul_right] at h'
    rw [tsum_geometric_of_lt_one] at h'
    have e := congrArg ( fun (n) => ((n) * ((1 - r) : ℝ))) h; beta_reduce at e
    rw [← one_div] at e
    rw [show  1 / (1 - ↑r) * (a : ℝ)  * (1 - ↑r)  =  (1 - ↑r) / (1 - ↑r) * a  by ring_nf] at e
    rw [div_self] at e
    simp at e
    rw [← one_div] at h'
    rw [e] at h'
    rw [show (1 : ℝ) / (1 - ↑r ^ 2) * (2000 * (1 - ↑r)) ^ 2 =  (2000 * 2000 * (1 - ↑r)* (1 - ↑r))  / (1 ^ 2 - ↑r ^ 2)  by ring_nf ] at h'
    rw [sq_sub_sq] at h'
    rw [mul_div_mul_right] at h'
    --\left({a\over{1+r}}\right)=S\cdot{a\over{1+r}}$.  Then $16=\displaystyle{a\over{1+r}}$ and $S=\displaystyle{a\over{1-r}}$ imply that $S(1-r)=16(1+r)$, so $r=\displaystyle{{S-16}\over{S+16}}=\frac{1984}{2016}=\frac{62}{63}$, and $m+n=62+63=\boxed{125}$.
    have  e2 := congrArg ( fun (n) => ((n) * ((1 + r) : ℝ))) h'; beta_reduce at e2
    rw [show  (2000 : ℝ )* 2000 * (1 - ↑r) / (1 + ↑r) * (1 + ↑r) =  2000 * 2000 * (1 - ↑r)  * ((1 + ↑r)  / (1 + ↑r) )by ring_nf] at e2
    rw [div_self] at e2
    ring_nf at e2
    norm_cast at e2
    have e3 := congrArg ( fun (n) => (((n) + r * (4000000 : ℚ ) - 32000)) / 4032000) e2; beta_reduce at e3; ring_nf at e3
    symm at e3;
    have e4 := Rat.divInt_eq_div 62 63
    have hr3 : Rat.divInt 62 63 = r  := by
      rw [e3]; rw [e4]
      norm_cast
    rw [← hr3]
    rw[Rat.num_mk];rw[Rat.den_mk]
    ring_nf
    rw[Int.sign.eq_def]
    norm_num
    norm_cast; linarith
    norm_cast; linarith
    norm_cast; linarith
    norm_cast; apply sq_nonneg
    rw[sq_lt_one_iff]
    norm_cast; norm_cast
    apply NormedRing.summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs]; norm_num; norm_cast; rw [abs_lt]
    constructor
    linarith
    linarith
    apply NormedRing.summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs]; norm_cast; rw [abs_lt]
    constructor
    linarith
    linarith
