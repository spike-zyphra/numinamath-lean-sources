import Mathlib

open Finset Real Polynomial

/- 16. (GDR 1) Let $F(n)$ be the set of polynomials $P(x)=a_{0}+a_{1} x+\cdots+a_{n} x^{n}$, with $a_{0}, a_{1}, \ldots, a_{n} \in \mathbb{R}$ and $0 \leq a_{0}=a_{n} \leq a_{1}=a_{n-1} \leq \cdots \leq a_{[n / 2]}=$ $a_{[(n+1) / 2]}$. Prove that if $f \in F(m)$ and $g \in F(n)$, then $f g \in F(m+n)$. -/
theorem algebra_23868 (F: ℕ → Set ℝ[X])
  (hF : ∀n, F n = {P: ℝ[X] | P.natDegree ≤ n ∧ ∀i,  i ≤ n → P.coeff i = P.coeff (n - i) ∧ P.coeff i ≥ 0}) :
  ∀n m, ∀f ∈ F m, ∀g ∈ F n, f * g ∈ F (m + n):= by
  intro n m f hf g hg
  have h_zero {n: ℕ}: 0 ∈ F n := by
    rw [hF]; simp
  -- we can construct the convex cone for F
  let convex_F (n: ℕ): ConvexCone ℝ ℝ[X] := by
    apply ConvexCone.mk (F n)
    · -- a convex cone should be closed under scalar multiplication
      intro c hc P hP
      rw [hF]; rw [hF] at hP
      simp; simp at hP
      obtain ⟨P_deg, gP⟩ := hP
      apply And.intro
      · rw [Polynomial.natDegree_smul]
        exact P_deg
        linarith
      · intro i hi
        specialize gP i hi
        constructor
        · left; apply gP.1
        · obtain ⟨_, gP_pos⟩ := gP
          apply mul_nonneg (le_of_lt hc) gP_pos
    · -- a convex cone should be closed under addition
      intro P hP Q hQ
      rw [hF] at hP hQ; rw [hF]
      obtain ⟨hP_deg, _⟩ := hP
      obtain ⟨hQ_deg, _⟩ := hQ
      rw [hF] at hf hg
      simp
      simp at hf hg
      constructor
      · apply le_trans (Polynomial.natDegree_add_le P Q)
        simp
        refine ⟨hP_deg, hQ_deg⟩
      · rename_i hr hr'
        intro i hi
        specialize hr i hi
        specialize hr' i hi
        obtain ⟨hr_symm, hr_pos⟩ := hr
        obtain ⟨hr'_symm, hr'_pos⟩ := hr'
        apply And.intro
        · simp [hr_symm, hr'_symm]
        · linarith
  -- zero is in this convex cone
  have h_zero_mem: ∀n, 0 ∈ F n := by simp [hF]
  have h_carrier: ∀n, F n = (convex_F n).carrier := by
    intro n; rfl
  -- let G represents the `basis` of the convex cone
  let G (n: ℕ) (i: ℕ): ℝ[X] := X^i + X^(n - i)
  -- and G will be within the polynomial space F n up to degree n
  have h_same {n: ℕ}: ∀i, i≤n → X^i + X^(n - i) ∈ F n := by
    intro i hi
    rw [hF]
    -- we show that indeed G n i = X^i + X^(n - 1) satisfies the conditions of F n
    constructor
    · -- first, G n i's degree is n
      apply le_trans
      · apply Polynomial.natDegree_add_le
      · simp; linarith
    · -- next G n i's coefficients are symmetric
      intro j hj
      -- now by cases of whether j is i, n - i or not
      by_cases H: (j = i ∨ j = (n - i))
      · -- if j = i, then G n i's coefficient at j is 1
        rcases H with H | H
        · simp [H, add_comm]
          apply And.intro
          · -- first the ite is the same
            apply ite_congr (by simp; constructor <;> tauto) (by simp) (by simp)
          · -- next the coefficient is positive by examining both cases H'
            by_cases H': i = n - i
            · simp [if_pos H']
            · simp [if_neg H']
        · simp [H]
          by_cases H': n - i = i
          · simp [H']
          · rw [if_neg, if_pos, if_neg] <;> (first|simp|omega)
      · -- otherwise j = n - i
        simp at H
        simp
        rw [if_neg H.1, if_neg, if_neg, if_neg]
        · simp
        · contrapose! H
          -- in the first case, j = i
          have H': j = i := by omega
          subst j
          simp
        · -- by contrapositive, suppose n - j = i
          contrapose! H
          -- then j = n - i
          have H': j = n - i := by omega
          subst j
          simp
        · -- by contrapositive, suppose j = n - i
          contrapose! H
          subst j
          simp
  have h_G {n: ℕ} (i: ℕ) (hi: i ≤ n): G n i ∈ F n := by
    apply h_same i hi
  -- next, we show that every polynomial in F n can be divided into linear combinations of G n i
  have h_F {n:ℕ}: ∀P ∈ F n, ∃(a : ℕ → ℝ),
    (∀i, i ≤ n → a i = a (n - i)) ∧
    (∀i, i ≤ n → a i ≥ 0) ∧
    ((2:ℝ) • P = ∑ i ∈ range (n + 1), a i • (G n i)) := by
    intro P h_P
    simp [hF] at h_P
    obtain ⟨P_deg, h_coeff⟩ := h_P
    use P.coeff
    refine ⟨?_, ⟨?_, ?_⟩⟩
    · -- first we show that the coefficients are symmetric
      intro i hi
      -- we adopt the symmetric coefficients properties from P
      specialize h_coeff i hi
      apply h_coeff.1
    · -- then the coefficients are non-negative
      intro i hi
      -- we adopt the non-negative coefficients properties from P
      specialize h_coeff i hi
      apply h_coeff.2
    · -- we start proving the equality of the polynomial by splitting up G
      simp [G]
      rw [Finset.sum_add_distrib]
      -- first we rearrange the X^(n-x) to X^x
      conv_rhs => right; rw [←Finset.sum_range_reflect]
      -- and then we show the summation is the same as the original polynomial
      have h: ∑ j ∈ range (n + 1), P.coeff (n + 1 - 1 - j) • X ^ (n - (n + 1 - 1 - j)) = (∑ j ∈ range (n + 1), P.coeff j • (X:ℝ[X]) ^ j) := by
        apply Finset.sum_congr rfl
        simp
        intro j hj
        -- we can write P.coeff n - i as P.coeff i as part of the symmetric coefficients
        specialize h_coeff j (by linarith)
        -- this allows us to cancel out the coefficients
        rw [h_coeff.1]
        -- next we show that X^(n- (n - j)) = X^j
        have : n - (n - j) = j := by omega
        simp [this]
      rw [h]
      -- next we expand the polynomian in terms of summation of monomial
      conv_lhs =>
        rw [Polynomial.as_sum_range' P (n + 1) (by omega)]
        rfl
      -- and we convert the 2 from real to a natural number
      norm_cast
      simp [two_mul]
      -- the we show that both side of the sum is the same
      congr 1 <;> (apply Finset.sum_congr rfl; unfold Polynomial.X; simp [Polynomial.smul_monomial])
  -- we can split the multiplication into two parts for any two G m and G n
  have h_mul {n m i j: ℕ} (h1: i ≤ n) (h2: j ≤ m): (G n i) * (G m j) = (G (m + n) (i + j)) + G (m + n) (m - j + i) := by
    unfold G
    ring_nf
    simp [<-pow_add]
    have h: n - i + (m - j) = (m + n) - i - j := by omega
    have h': m + n - (i + (m - j)) = n - i + j := by omega
    have h'': m + n - (i + j) = m + n - i - j := by omega
    simp [h, h', h'']
    ring_nf
  -- we next extract the symmetric coefficients for f and g
  obtain ⟨a, ha_symm, ha_pos, ha_sum⟩ :=  h_F f hf
  obtain ⟨b, hb_symm, hb_pos, hb_sum⟩ :=  h_F g hg
  -- next we divide both side by 2 to get f and g in terms of the summation
  have ha_sum': f = ((1:ℝ)/2) • (∑ i ∈ range (m + 1), a i • G m i) := by simp [←ha_sum]
  have hb_sum': g = ((1:ℝ)/2) • (∑ i ∈ range (n + 1), b i • G n i) := by simp [←hb_sum]
  -- we then substitute f and g, and then expand the product of the summation
  simp [ha_sum', hb_sum', Finset.sum_mul_sum]
  -- since the whole sum is a smul, we show it being a convex cone from the non scalar product part
  generalize hFmn: convex_F (m + n) = F_m_n
  have h₁ := F_m_n.add_mem'
  -- we show that the summation is closed in F (m + n)
  have h_closed_sum₀: ∀(a:ℝ), ∀m', ∀(f: ℕ → ℝ[X]), a > 0 → (∀i ∈ range m', f i ∈ F (m + n)) → (a • ∑ i ∈ range m', f i) ∈ F (m + n) := by
    intro a m' f h_a_pos hf
    -- induction by m', where we split the summation
    revert a
    induction m'
    · simp [h_zero_mem]
    · rename_i n' a_ih
      -- f i is in F (m + n) in the induction hypothesis, leveraging hf covering n' + 1
      have hf': ∀ i ∈ range n', f i ∈ F (m + n) := by
        -- hi state that i is in the range of m'
        intro i hi
        -- hf states that f i is in F (m + n) for all i in range m' + 1
        specialize hf i
        apply hf
        simp
        simp at hi
        linarith
      -- from the induction hypothesis, the sum over first n' terms are in F (m + n)
      specialize a_ih hf'
      -- we then split the last term in the summation
      rw [Finset.sum_range_succ, h_carrier, hFmn]
      rw [h_carrier, hFmn] at a_ih
      -- convex cone is closed under scalar multiplication
      intro a h_a_pos
      apply F_m_n.smul_mem' h_a_pos
      -- and convex cone is closed under addition
      specialize a_ih 1 (by simp)
      simp at a_ih
      apply F_m_n.add_mem' a_ih
      rw [h_carrier, hFmn] at hf
      -- then we leverage hf at n'
      specialize hf n' (by simp)
      apply hf
  -- we first show an auxiliary lemma, stating that the summation of multiplication of G n i and G m j are closed for F (m + n)
  have h_closed_sum₁: ∀m' n', m' ≤ m + 1 → n' ≤ n + 1 → ∀ i ∈ range m', ∑ j ∈ range (n'), a i • G m i * b j • G n j ∈ F (m + n) := by
    intro m' n' hm' hn' i hi
    induction n'
    · -- 0 is a special case and it is in F (m + n)
      apply h_zero_mem
    · -- then the induction case
      rename_i n' a_ih
      -- we can split the last element within the sum
      rw [Finset.sum_range_succ, h_carrier, hFmn]
      -- we then show that sum is in the convex cone
      apply F_m_n.add_mem'
      · -- first with induction hypothesis, the sum over first n' terms are in F (m + n)
        rw [h_carrier, hFmn] at a_ih
        exact a_ih (by linarith)
      · -- next,  i • G m i * b n' • G n n' = b n' • a i • (G m i * G n n') is also in F (m + n)
        simp
        -- first we eliminate the scalar multiplication by enumeratig whether b n' * a i = 0 or not
        simp [←smul_assoc]
        rcases (eq_or_ne (b n' * a i) 0) with H | H
        · -- if b n' * a i = 0, then the product is 0 and is in F (m + n)
          simp [H, ←hFmn]
          apply h_zero_mem
        · -- firstly, b n' >= 0
          specialize hb_pos n' (by omega)
          -- and also a i >= 0
          specialize ha_pos i (by simp at hi; linarith)
          -- next we show that (b n' * a i) • (G m i * G n n') is in F (m + n)
          apply F_m_n.smul_mem'
          · -- first the scalar coefficient is positive
            simp at H
            obtain ⟨H_b_ne_zero, H_a_ne_zero⟩ := H
            apply mul_pos
            · contrapose! H_b_ne_zero; linarith
            · contrapose! H_a_ne_zero; linarith
          · -- next we show G m i * G n n'  is in F (m + n) by first rewriting it as G (n + m) (i + n') + G (n + m) (n - n' + i)
            rw [h_mul (by simp at hi; linarith) (by omega)]
            -- then we show that both terms are in F (m + n)
            apply F_m_n.add_mem'
            · -- first G (n + m) (i + n') ∈ F_m_n.carrier
              specialize h_G (n := n + m) (i := i + n') (by simp at hi; omega)
              rw [h_carrier, add_comm, hFmn, add_comm] at h_G
              apply h_G
            · -- next G (n + m) (n - n' + i) ∈ F_m_n.carrier
              specialize h_G (n := n + m) (i := n - n' + i) (by simp at hi; omega)
              rw [h_carrier, add_comm, hFmn, add_comm] at h_G
              apply h_G
  · -- it suffices to show that ∑ i ∈ range (m / 2), ∑ j ∈ range (n / 2), a i • G m i * b j • G n j ∈ F (m + n)
    simp [←smul_assoc]
    apply h_closed_sum₀
    -- 1/2 * 1/2 > 0
    simp
    -- we specialize h_closed_sum₁ so that it is summed over the range of m / 2 and n / 2
    specialize h_closed_sum₁ (m + 1) (n + 1) (by simp) (by simp)
    simp
    simp at h_closed_sum₁
    -- and finally we can close the goal leveraging h_closed_sum₁
    intro i hi
    specialize h_closed_sum₁ i hi
    -- we also need to eliminate the smul in the summation
    conv at h_closed_sum₁ =>
      enter [2, 2]
      ext j
      simp [←smul_assoc]
    -- and we can now apply h_closed_sum₁
    convert h_closed_sum₁
