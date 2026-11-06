import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- Find all positive integers  $b$  with the following property:
there exists positive integers  $a,k,l$  such that
  $a^k + b^l$  and  $a^l + b^k$  are divisible by  $b^{k+l}$  where  $k \neq l$ .-/
theorem number_theory_8946 :
  {b : ℕ | 0 < b ∧ ∃ a k l : ℕ, 0 < a ∧ 0 < k ∧ 0 < l ∧
  k ≠ l ∧ b^(k + l) ∣ a^k + b^l ∧ b^(k + l) ∣ a^l + b^k} = {1} := by
  ext b
  constructor
  . intro hb
    rcases hb with ⟨hbpos, a, k, l, hapos, hkpos, hlpos, hkl, hb1, hb2⟩
    by_contra hb
    change _ ≠ _ at hb
    -- n | m means vp(n) ≤ vp(m)
    rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)] at hb1
    rw [← Nat.factorization_prime_le_iff_dvd (by positivity) (by positivity)] at hb2
    -- Suffices to show that there exists a prime number p such that
    -- min(vp(a^k+b^l), vp(a^l+b^k)) < vp(b^(k+1))
    suffices ∃ p : ℕ, p.Prime ∧ min (padicValNat p (a^k+b^l)) (padicValNat p (a^l+b^k)) <
        padicValNat p (b^(k+l)) by
      obtain ⟨p, hpp, hplt⟩ := this
      rw [min_lt_iff] at hplt
      rcases hplt with h | h
      . specialize hb1 p hpp
        repeat rw [Nat.factorization_def _ hpp] at hb1
        linarith
      specialize hb2 p hpp
      repeat rw [Nat.factorization_def _ hpp] at hb2
      linarith
    -- Since b≠1, there exists a prime number p such that p|b.
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hb
    use p
    refine ⟨hp, ?_⟩
    have : Fact p.Prime := ⟨hp⟩
    have pval_pos_of_pdvd {n : ℕ} (hn : 0 < n) (hpn : p ∣ n) : 0 < padicValNat p n := by
      exact one_le_padicValNat_of_dvd hn hpn
    have : k^2 ≠ l^2 := by
      intro hk
      simp at hk
      contradiction
    -- If  $k\nu_p(a)=\nu_p(a^k)=\nu_p(b^l)=l\nu_p(b)$ ,
    -- then  $\nu_p(a^l)=l\nu_p(a)=\frac{l^2}k\nu_p(b)\neq k\nu_p(b)=\nu_p(b^k)$  since  $k^2\neq l^2$ .
    -- Therefore, either  $\nu_p(a^k)\neq\nu_p(b^l)$  or  $\nu_p(a^l)\neq\nu_p(b^k)$ .
    have not_all_eq : padicValNat p (a^l) ≠ padicValNat p (b^k) ∨
        padicValNat p (a^k) ≠ padicValNat p (b^l) := by
      by_contra h
      push_neg at h
      repeat rw [padicValNat.pow _ (by positivity)] at h
      rcases h with ⟨h1, h2⟩
      apply_fun (k * ·) at h1
      rw [← mul_assoc, mul_comm k, mul_assoc, h2, ← mul_assoc, ← mul_assoc,
        mul_left_inj', ← pow_two, ← pow_two, eq_comm] at h1
      contradiction
      . rw [← Nat.pos_iff_ne_zero]
        exact pval_pos_of_pdvd hbpos hpdvd
    zify at not_all_eq ⊢
    -- $\therefore\min(\nu_p(a^k+b^l), \nu_p(a^l+b^k))\leq\max(\min(\nu_p(a^k), \nu_p(b^l)), \min(\nu_p(a^l), \nu_p(b^k)))\leq\max(\nu_p(b^l), \nu_p(b^k))<\nu_p(b^{k+l})$ .
    -- $\Rightarrow b^{k+l}$  cannot divide both  $a^k+b^l$  and  $a^l+b^k$ . $\therefore$  the only possible  $b$  is  $1$ .
    rcases not_all_eq with h | h
    . apply min_lt_of_right_lt
      rw [padicValRat.add_eq_min (by positivity) (by positivity) (by positivity) h]
      apply min_lt_of_right_lt
      norm_cast
      repeat rw [padicValNat.pow _ (by positivity)]
      rw [Nat.mul_lt_mul_right <| pval_pos_of_pdvd hbpos hpdvd]
      omega
    . apply min_lt_of_left_lt
      rw [padicValRat.add_eq_min (by positivity) (by positivity) (by positivity) h]
      apply min_lt_of_right_lt
      norm_cast
      repeat rw [padicValNat.pow _ (by positivity)]
      rw [Nat.mul_lt_mul_right <| pval_pos_of_pdvd hbpos hpdvd]
      omega
  -- Verify b=1 is solution.
  . intro hb
    change _ = _ at hb
    rw [hb]
    constructor
    . norm_num
    . use 1, 1, 2
      split_ands <;> norm_num
