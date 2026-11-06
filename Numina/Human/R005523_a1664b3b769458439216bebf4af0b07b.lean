import Mathlib

open Polynomial

namespace algebra_608635

/- If the degree of a nonzero polynomial `p` is less than or equal to the root multiplicity of `a`, then `p` is associated with `(X - C a) ^ p.natDegree`. -/
lemma associated_pow_X_sub_C_of_natDegree_le {K : Type*} [Field K]
    {p : K[X]} (hp : p ≠ 0) {a : K} (ha : p.natDegree ≤ rootMultiplicity a p) :
    Associated ((X - C a) ^ p.natDegree) p := by
  rw [Polynomial.le_rootMultiplicity_iff hp] at ha
  apply associated_of_dvd_of_natDegree_le ha hp
  nth_rw 1 [← Polynomial.natDegree_X_pow_sub_C (n := p.natDegree) (r := a)]
  simp only [natDegree_sub_C, natDegree_pow, natDegree_X, mul_one, le_refl]

/- For a complex polynomial `p`, `p.natDegree` equals `p.roots.card`. -/
lemma natDegree_eq_card_roots_complex (p : ℂ[X]) : p.natDegree = p.roots.card := by
  simpa only [map_id] using Polynomial.natDegree_eq_card_roots' (IsAlgClosed.splits p)

/- For a nonzero polynomial `p` over an integral domain, 
the sum of the root multiplicities of two distinct roots `a` and `b` is less than or equal to the total number of roots. -/
lemma add_rootMultiplicity_le_card_roots {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    {p : R[X]} {a b : R} (hab : a ≠ b) (ha : a ∈ p.roots) (hb : b ∈ p.roots) :
    rootMultiplicity a p + rootMultiplicity b p ≤ p.roots.card := by
  repeat rw [← count_roots]
  refine LE.le.trans_eq ?_ (Multiset.sum_count_eq_card (s := p.roots.toFinset) (by simp))
  refine Finset.add_le_sum (f := p.roots.count) ?_ ?_ ?_ hab <;> simp_all

/-For `algebra_608635`, `p.derivative` has a double root-/
theorem rootMultiplicity_of_derivative_root_eq_two {p : ℂ[X]} (hp : p.natDegree = 3)
  (h : ∀ t, (p.derivative).IsRoot t → p.IsRoot t) {a : ℂ} (ha : p.derivative.IsRoot a) :
  rootMultiplicity a (p.derivative) = 2 := by
  have hp1 : p.degree = 3 := by
    rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num)] at hp
    simp [hp]
  have hp2 : p ≠ 0 := by
    rw [← degree_ne_bot]
    rw [hp1]
    simp
  have hp'1 : (p.derivative).degree = 2 := by
    rw [Polynomial.degree_derivative_eq]
    <;> simp [hp]
  have hp'2 : (p.derivative) ≠ 0 := by
    rw [← degree_ne_bot]
    rw [hp'1]
    simp only [ne_eq, WithBot.ofNat_ne_bot, not_false_eq_true]
  have hp'3 : (p.derivative).natDegree = 2 :=
    (degree_eq_iff_natDegree_eq hp'2).mp hp'1
  have hp'4 := natDegree_eq_card_roots_complex p.derivative
  rw [hp'3] at hp'4
  suffices ∀ b ∈ (derivative p).roots, a = b by
    rw [← count_roots, hp'4]
    rw [Multiset.count_eq_card]
    exact this
  intro b hb
  simp only [mem_roots', ne_eq, hp'2, not_false_eq_true, true_and] at hb
  have ha1 := h a ha
  have hb1 := h b hb
  by_contra hab
  -- A root of a polynomial $p$ will be a double root if and only if it is also a root of $p^{\prime}$
  -- Let $a$ and $b$ be the roots of $p^{\prime}$. 
  -- Since $a$ and $b$ are also roots of $p$, they are double roots of $p$. 
  have ha2 := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp2).2 ⟨ha1, ha⟩
  have hb2 := (Polynomial.one_lt_rootMultiplicity_iff_isRoot hp2).2 ⟨hb1, hb⟩
  -- $p$ can have only at most three roots,
  have hp3 : p.roots.card ≤ 3 := by
    rw [← hp]
    exact Polynomial.card_roots' p
  absurd hp3
  clear* -ha1 hb1 hab ha2 hb2 hp2
  suffices rootMultiplicity a p + rootMultiplicity b p ≤ p.roots.card by
    linarith only [ha2, hb2, this]
  replace ha1 : a ∈ p.roots := by
    simp only [mem_roots']
    exact ⟨hp2, ha1⟩
  replace hb1 : b ∈ p.roots := by
    simp only [mem_roots']
    exact ⟨hp2, hb1⟩
  -- But $p$ can have only three roots, so $a=b$ and $a$ becomes a double root of $p^{\prime}$. 
  exact add_rootMultiplicity_le_card_roots hab ha1 hb1

end algebra_608635

open algebra_608635

/-Let $p$ be a monic cubic polynomial such that $p(0)=1$ and such that
all the zeros of $p^{\prime}(x)$ are also zeros of $p(x)$.
Find $p$. Note: monic means that the leading coefficient is 1 .-/
theorem algebra_608635 {p : ℂ[X]} (hp : p.natDegree = 3) (h1 : eval 0 p = 1)
    (h2 : Monic p) (h : ∀ t, (p.derivative).IsRoot t → p.IsRoot t) :
    ∃ a : ℂ, a ^ 3 = -1 ∧ p = (X - C a) ^ 3 := by
  have hp'1 : (p.derivative).natDegree = 2 := by
    rw [← degree_eq_iff_natDegree_eq_of_pos (by norm_num)]
    rw [Polynomial.degree_derivative_eq]
    <;> simp [hp]
  have hp'2 : 0 < (p.derivative).degree := by
    rw [← natDegree_pos_iff_degree_pos]
    simp [hp'1]
  obtain ⟨a, ha1⟩ := Complex.exists_root hp'2
  have ha2 := h a ha1
  -- $a$ becomes a double root of $p^{\prime}$.
  -- This makes $p^{\prime}(x)=u(x-a)^{2}$ for some unit $u$.
  have ha3 : Associated ((X - C a) ^ 2) p.derivative := by
    rw [← hp'1]
    apply associated_pow_X_sub_C_of_natDegree_le
    · exact ne_zero_of_degree_gt hp'2
    · rw [rootMultiplicity_of_derivative_root_eq_two hp h ha1]
      rw [hp'1]
  obtain ⟨c, hc⟩ := ha3
  have hc := c.isUnit
  rw [Polynomial.isUnit_iff] at hc
  obtain ⟨u, hu1, hu2⟩ := hc
  rw [← hu2] at hc
  have coeff2_eq : ((X - C a) ^ 2).coeff 2 = 1 := by
    noncomm_ring ; simp
  have coeff1_eq : ((X - C a) ^ 2).coeff 1 = -2 * a := by
    noncomm_ring ; simp only [Int.reduceNeg, neg_smul, one_smul, X_mul_C, coeff_add, coeff_mul_X,
      coeff_X_zero, coeff_neg, coeff_C_zero, coeff_mul_C, coeff_C_succ, zero_mul, add_zero,
      zero_add, zsmul_eq_mul, Int.cast_ofNat] ; ring
  have coeff3_eq : ((X - C a) ^ 2).coeff 0 = a ^ 2 := by
    noncomm_ring ; simp
  have h_deriv_coeff2 := Polynomial.coeff_derivative p 2
  have h_deriv_coeff1 := Polynomial.coeff_derivative p 1
  have h_deriv_coeff0 := Polynomial.coeff_derivative p 0
  rw [← hc] at h_deriv_coeff2 h_deriv_coeff1 h_deriv_coeff0
  simp only [coeff_mul_C, Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, mul_coeff_zero, coeff_C_zero,
    zero_add, CharP.cast_eq_zero, mul_one] at h_deriv_coeff2 h_deriv_coeff1 h_deriv_coeff0
  rw [coeff2_eq] at h_deriv_coeff2
  rw [coeff1_eq] at h_deriv_coeff1
  rw [coeff3_eq] at h_deriv_coeff0
  -- Because $p (0) =1$ and $p$ is monic, $u=3$ 
  have h_coeff0 : p.coeff 0 = 1:= by
    rw [← h1]
    exact (coeff_zero_eq_eval_zero p)
  have h_coeff3 : p.coeff 3 = 1 := by
    rw [← hp]
    rw [coeff_natDegree]
    exact h2
  have hu3 : u = 3 := by
    simp only [one_mul, h_coeff3] at h_deriv_coeff2
    rw [h_deriv_coeff2]
    norm_num
  subst hu3
  replace h_deriv_coeff1 : p.coeff 2 = -3 * a := by
    rw [show p.coeff 2 = 1 / 2 * (p.coeff 2 * (1 + 1)) by ring]
    rw [← h_deriv_coeff1]
    ring
  -- and then $p(x) = x³ - 3ax²+3a²x+1$.
  have hp : p = X ^ 3 - 3 * C a * X ^ 2 + 3 * C (a ^ 2) * X + 1 := by
    ext n
    match n with
    | 0 =>
      rw [h_coeff0]
      simp
    | 1 =>
      rw [← h_deriv_coeff0]
      noncomm_ring
      simp only [zsmul_eq_mul, Int.cast_ofNat, Int.reduceNeg, neg_smul, map_mul, coeff_add,
        coeff_X_mul, mul_coeff_zero, coeff_X_zero, mul_zero, coeff_neg, coeff_ofNat_mul,
        coeff_C_mul, coeff_mul_X, neg_zero, coeff_C_zero, zero_add, self_eq_add_right]
      apply coeff_eq_zero_of_natDegree_lt
      simp
    | 2 =>
      rw [h_deriv_coeff1]
      noncomm_ring
      simp only [Int.reduceNeg, neg_smul, zsmul_eq_mul, Int.cast_ofNat, map_mul, coeff_add,
        coeff_X_mul, coeff_mul_X, coeff_X_zero, coeff_neg, coeff_ofNat_mul, coeff_C_mul,
        coeff_X_one, mul_one, coeff_mul_C, coeff_C_succ, zero_mul, mul_zero, zero_add,
        self_eq_add_right]
      apply coeff_eq_zero_of_natDegree_lt
      simp
    | 3 =>
      rw [h_coeff3, eq_comm]
      compute_degree!
    | n + 4 =>
      have coeff1 : p.coeff (n + 4) = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hp]
        norm_num
      have coeff2 : (X ^ 3 - 3 * C a * X ^ 2 + 3 * C (a ^ 2) * X + 1).coeff (n + 4) = 0 := by
        compute_degree!
        simp only [Nat.reduceEqDiff, ↓reduceIte, CharP.cast_eq_zero, sub_self, add_zero]
      rw [coeff1, coeff2]
  use a
  -- From $p(a)=0$ we get $a³ = -1$ and $p(x)=(x+a)³$
  have ha : a ^ 3 = -1 := by
    rw [hp] at ha2
    simp only [map_pow, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat,
      eval_C, eval_one] at ha2
    ring_nf at ha2
    rw [← sub_eq_zero, sub_neg_eq_add, add_comm]
    exact ha2
  clear* -ha hp
  constructor
  · exact ha
  · rw [hp]
    apply Polynomial.funext
    intro x
    simp only [map_pow, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat, eval_C,
      eval_one]
    ring_nf
    rw [ha]
    ring