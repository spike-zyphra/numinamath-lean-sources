import Mathlib

open Polynomial

/- For distinct complex numbers $z_1,z_2,\dots,z_{673}$, the polynomial
$$
(x-z_1)^3(x-z_2)^3 \cdots (x-z_{673})^3
$$
can be expressed as $x^{2019} + 20x^{2018} + 19x^{2017}+g(x)$, where $g(x)$ is a polynomial with complex coefficients and with degree at most $2016$. The sum
$$
\left| \sum_{1 \le j < k \le 673} z_jz_k \right|
$$
can be expressed in the form $\frac{m}{n}$, where $m$ and $n$ are relatively prime positive integers. Find $m+n$. -/

theorem algebra_97723 (z : Fin 673 → ℂ)
    (g : Polynomial ℂ) (hg : g.degree ≤ 2016)
    (h : ∀ x, ∏ i : Fin 673, (x - z i)^3 = x^2019 + 20 * x^2018 + 19 * x^2017 + g.eval x)
    {m n : ℕ} (hm : m > 0) (hn : n > 0) (hmn : m.Coprime n)
    (hsum : Complex.abs (∑ i : Fin 673, ∑ j : Fin 673, if i < j then z i * z j else 0) = m / n) :
    m + n = 352 := by
  -- it is more convenient to work with sequences indexed by ℕ
  -- so define zn(i) = z(i) for i < 673
  set zn : ℕ → ℂ := fun i => if h : i < 673 then z ⟨i, h⟩ else 0
  have hzn {i : ℕ} (hi : i < 673) : zn i = z ⟨i, hi⟩ := by simp [zn, hi]
  -- define p = (∏ i ∈ range 673, (X - C (zn i))) ^ 3
  set p : Polynomial ℂ := (∏ i ∈ Finset.range 673, (X - C (zn i))) ^ 3
  -- we have p = X ^ 2019 + 20 * X ^ 2018 + 19 * X ^ 2017 + g
  replace h : p = X ^ 2019 + 20 * X ^ 2018 + 19 * X ^ 2017 + g := by
    apply Polynomial.funext
    intro x
    simp only [eval_pow, eval_prod, eval_sub, eval_X, eval_C, eval_add, eval_mul, eval_ofNat, p]
    rw [←h x, Finset.prod_pow, Finset.prod_fin_eq_prod_range]
    congrm ?_ ^ 3
    apply Finset.prod_congr rfl
    simp
    intro i hi
    simp [hi, hzn]
  replace hg : g.natDegree ≤ 2016 := natDegree_le_of_degree_le hg
  have hg_coeff {n} (hn : 2017 ≤ n) : g.coeff n = 0 := by
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
  have hp_deg : p.natDegree = 2019 := by
    simp [h]
    compute_degree! <;> try omega
    rw [hg_coeff (by norm_num)]
    norm_num
  have hp_monic : p.Monic := by
    rw [Monic, leadingCoeff, hp_deg]
    simp [h, hg_coeff]
  have hp1 : p.nextCoeff = 20 := by
    simp [nextCoeff, hp_deg]
    simp [h, hg_coeff]
  have hp2 : p.coeff 2017 = 19 := by simp [h, hg_coeff]
  have fin_range (n : ℕ) : (Finset.range n).val = Multiset.range n := rfl
  -- it is easy to show that all roots of p are zn(i) (for i < 673) taken three times each
  have hp_roots : p.roots = 3 • Multiset.map zn (Multiset.range 673) := by
    dsimp [p]
    rw [roots_pow]
    congrm 3 • ?_
    suffices h : ∏ i ∈ Finset.range 673, (X - C (zn i)) = (Multiset.map (fun r => X - C r) <| Multiset.map zn (Finset.range 673).val).prod by
      rw [h, Polynomial.roots_multiset_prod_X_sub_C, fin_range]
    clear * -
    rw [Finset.prod_eq_multiset_prod, Multiset.map_map]
    congr
  -- define s1 = ∑ i ∈ range 673, zn i (the sum of all values of zn)
  set s1 := ∑ i ∈ Finset.range 673, zn i
  -- define s2 = ∑ i ∈ range 673, zn i ^ 2 (the sum of squares of values of zn)
  set s2 := ∑ i ∈ Finset.range 673, zn i ^ 2
  -- s is the sum which we need to compute
  set s := ∑ i ∈ Finset.range 673, ∑ j ∈ Finset.range 673, if i < j then zn i * zn j else 0
  replace hsum : Complex.abs s = m / n := by simp [← hsum, s, ← Fin.sum_univ_eq_sum_range, ←hzn]
  -- use Vieta's formula to find that
  -- s1 = the sum of roots / 3 = -p.coeff 2018 / 3 = -20 / 3
  have hs1 : s1 = -20 / 3 := calc
    s1 = (3 * s1) / 3 := by simp
    _  = p.roots.sum / 3 := by
      rw [hp_roots, Multiset.sum_nsmul, nsmul_eq_mul]
      rfl
    _  = -p.nextCoeff / 3 := by rw [sum_roots_eq_nextCoeff_of_monic_of_split hp_monic (IsAlgClosed.splits _), neg_neg]
    _  = -20 / 3 := by rw [hp1]
  -- we want to use Vieta's formula for p.coeff 2017 = 19
  -- first of all, we need to prove some auxiliary results about elementary symmetric functions (esymm)
  -- esymm 2 computed at the elements of s taken three times each is equal to
  -- 9 * s.esymm 2 + 3 * (sum of squares of elements of s)
  have esymm2_nsmul (s : Multiset ℂ) : (3 • s).esymm 2 = 3 * (s.map (fun x => x ^ 2)).sum + 9 * s.esymm 2 := by
    induction s using Multiset.induction with
    | empty => simp [Multiset.esymm]
    | cons a s ih =>
      have eq : (3 • (a ::ₘ s)) = a ::ₘ a ::ₘ a ::ₘ (3 • s) := by
        ext x
        simp [Multiset.count_cons]
        split_ifs <;> omega
      simp [eq, Multiset.esymm, Multiset.powersetCard_one]
      rw [←Multiset.esymm, ih, ←Multiset.esymm]
      simp [Multiset.map_nsmul, Multiset.sum_nsmul]
      ring
  -- esymm 2 computed at the elements of f applied to range n has the same shape as the sum which we need to find (s)
  have esymm2_map_range (n : ℕ) (f : ℕ → ℂ) : (Multiset.map f (Multiset.range n)).esymm 2 =
      ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, if i < j then f i * f j else 0 := by
    clear * - fin_range
    simp [Multiset.esymm]
    induction n with
    | zero => simp
    | succ n ih =>
      simp [Multiset.powersetCard_one]
      rw [ih]
      clear ih
      rw [←fin_range, ←Finset.sum.eq_1]
      simp_rw [Finset.sum_range_succ, Finset.sum_add_distrib]
      set a := ∑ i ∈ _, ∑ j ∈ _, if i < j then f i * f j else 0
      set b := ∑ i ∈ _, f n * f _
      set c := ∑ i ∈ _, if _ < n then f _ * f n else 0
      set d := ∑ i ∈ _, if n < _ then f n * f _ else 0
      suffices h : b = c by
        simp [h]
        apply Finset.sum_eq_zero
        simp
        omega
      apply Finset.sum_congr rfl
      simp
      intro i hi
      simp [hi, mul_comm]
  -- now we can use Vieta's formula to show that 3 * s2 + 9 * s = 19
  have hs2 : 3 * s2 + 9 * s = 19 := by
    have h := coeff_eq_esymm_roots_of_splits (IsAlgClosed.splits p) (by omega : 2017 ≤ p.natDegree)
    rw [Monic.leadingCoeff hp_monic, hp_deg, hp2] at h
    rw [h]
    norm_num
    rw [hp_roots, esymm2_nsmul, Multiset.map_map, esymm2_map_range, ←fin_range, ←Finset.sum.eq_1]
    rfl
  -- prove that s1 ^ 2 = s2 + 2 * s
  have hs2' : s1 ^ 2 = s2 + 2 * s := by
    dsimp [s1, s2, s]
    generalize zn = f
    clear * -
    -- proof by induction: replace 673 with an arbitrary n
    generalize 673 = n
    induction n with
    | zero => simp
    | succ n ih =>
      simp [Finset.sum_range_succ]
      ring_nf
      rw [ih, Finset.sum_add_distrib]
      clear ih
      set a := ∑ i ∈ _, f i
      set b := ∑ i ∈ _, f i ^ 2
      set c := ∑ i ∈ _, ∑ j ∈ _, if i < j then f i * f j else 0
      set d := ∑ i ∈ _, if i < _ then f i * f _ else 0
      set e := ∑ i ∈ _, if _ < i then f _ * f i else 0
      have he : e = 0 := by
        apply Finset.sum_eq_zero
        simp
        intro i hi
        omega
      have hd : d = a * f n := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        simp
        intro i hi
        omega
      rw [he, hd]
      ring
  -- from s1 = -20 / 3, 3 * s2 + 9 * s = 19, and s1 ^ 2 = s2 + 2 * s
  -- we find that s = -343 / 9
  have hs_eq : s = -343 / 9 := calc
    s = (3 * s) / 3 := by simp
    _ = (9 * s - 3 * (2 * s)) / 3 := by ring
    _ = ((19 - 3 * s2) - 3 * (s1 ^ 2 - s2)) / 3 := by linear_combination hs2 / 3 + hs2'
    _ = (19 - 3 * s1 ^ 2) / 3 := by ring
    _ = -343 / 9 := by rw [hs1]; norm_num
  field_simp [hs_eq] at hsum
  clear * - hsum hn hm hmn
  -- we have |s| = 343 / 9 = n / n and it is left to show that m = 343 and n = 9
  suffices h : m = 343 ∧ n = 9 by simp [h]
  zify
  norm_cast at hsum
  apply Rat.div_int_inj
  any_goals norm_cast
  apply (NNRat.divNat_inj _ _).mpr
  all_goals linarith