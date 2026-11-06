import Mathlib
open Classical

/-
Let $f$ and $g$ be two nonzero polynomials with integer coefficients and $\operatorname{deg} f>\operatorname{deg} g$. Suppose that for infinitely many primes $p$ the polynomial $p f+g$ has a rational root. Prove that $f$ has a rational root.
-/
theorem algebra_24147 {f g : Polynomial ℤ} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfg : f.degree > g.degree) : {p : ℕ | Nat.Prime p ∧ Exists ((p * f + g).map (Int.castRingHom ℚ)).IsRoot}.Infinite → Exists (f.map (Int.castRingHom ℚ)).IsRoot := by
  intro hS
  set S := {p : ℕ | Nat.Prime p ∧ Exists (Polynomial.map (Int.castRingHom ℚ) (p * f + g)).IsRoot}

  -- One can assume that $f$ is monic.
  -- Indeed, let $f(x)=a_{n} x^{n}+a_{n-1} x^{n-1}+\cdots+a_{0}$ and $g(x)=b_{m} x^{m}+b_{m-1} x^{m-1}+\cdots+b_{0}$ where $n>m, a_{n} \neq 0$ and $b_{m} \neq 0$. Upon replacing $f(x)$ and $g(x)$ by $a_{n}^{n-1} f\left(x / a_{n}\right)$ and $a_{n}^{n-1} g\left(x / a_{n}\right)$ respectively, we reduce the problem to the case $a_{n}=1$.

  wlog hM : f.Monic
  · replace hfg := Polynomial.natDegree_lt_natDegree hg hfg
    set n := f.natDegree
    set m := g.natDegree
    let aₙ := f.leadingCoeff
    have ha : aₙ ≠ 0 := by
      simp [aₙ, Polynomial.leadingCoeff_eq_zero]
      exact hf
    let scale (g : Polynomial ℤ) := g.sum (fun k a => Polynomial.monomial k (aₙ^(n - 1 - k) * a))
    have scale_degree (g : Polynomial ℤ) : (scale g).natDegree ≤ g.natDegree := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro k _
      apply le_trans
      show (Polynomial.monomial k _).natDegree ≤ k
      apply Polynomial.natDegree_monomial_le
      apply Polynomial.le_natDegree_of_mem_supp
      assumption
    have scale_eval (g : Polynomial ℤ) : g.natDegree ≤ n - 1 → ∀ x : ℚ, Polynomial.eval x (Polynomial.map (Int.castRingHom ℚ) (scale g)) = aₙ^(n-1) * (Polynomial.eval (x/aₙ) (Polynomial.map (Int.castRingHom ℚ) g)) := by
      intro hg
      intro x
      simp [Polynomial.eval_map, scale, Polynomial.eval₂_sum, Polynomial.eval₂]
      simp [Polynomial.sum_over_range, Finset.mul_sum]
      apply Finset.sum_congr
      trivial
      intro k hk
      have : k ≤ n - 1 := by
        refine le_trans ?_ hg
        rwa [← Finset.mem_range_succ_iff]
      rw [pow_sub₀ (↑aₙ:ℚ) (by norm_cast) this]
      ring
    let f₂ := scale f.eraseLead
    let f₁ := (Polynomial.monomial n (1:ℤ)) + f₂
    let g₁ := scale g

    set gRat := Polynomial.map (Int.castRingHom ℚ) g
    set g₁Rat := Polynomial.map (Int.castRingHom ℚ) g₁
    have hgs : ∀ x : ℚ, Polynomial.eval x g₁Rat = aₙ^(n-1) * (Polynomial.eval (x/aₙ) gRat) := by
      apply scale_eval g
      exact Nat.le_pred_of_lt hfg

    set fRat := Polynomial.map (Int.castRingHom ℚ) f
    set f₁Rat := Polynomial.map (Int.castRingHom ℚ) f₁
    have hfs : ∀ x : ℚ, Polynomial.eval x f₁Rat = aₙ^(n-1) * (Polynomial.eval (x/aₙ) fRat) := by
      intro x
      simp [f₁Rat,f₁,fRat]
      rw [← f.eraseLead_add_monomial_natDegree_leadingCoeff]
      conv =>
        rhs
        rw [add_comm]
      simp [mul_add]
      congr
      · simp [aₙ,n]
        rw [← mul_assoc]
        rw [pow_sub_one_mul]
        field_simp
        exact Nat.not_eq_zero_of_lt hfg
      · apply scale_eval f.eraseLead
        apply Polynomial.eraseLead_natDegree_le
    have hf₂ : f₂.natDegree ≤ n - 1 := by
      apply le_trans
      apply scale_degree f.eraseLead
      apply Polynomial.eraseLead_natDegree_le
    have hfc : f₁.coeff n = 1 := by
      simp [f₁, Polynomial.coeff_monomial]
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      refine Nat.lt_of_le_pred ?_ hf₂
      refine lt_of_le_of_lt ?_ hfg
      simp
    have _ : f₁.natDegree ≤ n := by
      apply Polynomial.natDegree_add_le_of_degree_le
      apply Polynomial.natDegree_monomial_le
      apply le_trans hf₂
      norm_num
    have _ : f₁.natDegree = n := by
      apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      assumption
      linarith
    have hf₁ : f₁ ≠ 0 := by
      intro h
      apply congrArg (fun (pol : Polynomial ℤ) => pol.coeff n) at h
      simp [hfc] at h
    have hg₁ : g₁ ≠ 0 := by
      intro h
      simp [g₁, scale] at h
      apply congrArg (fun (pol : Polynomial ℤ) => pol.coeff g.natDegree) at h
      simp [Polynomial.coeff_monomial,Polynomial.sum] at h
      rcases h hg with j|j
      · absurd j.left
        exact ha
      · contradiction
    have hfM : f₁.Monic := by
      refine Polynomial.monic_of_natDegree_le_of_coeff_eq_one n ?_ hfc
      assumption
    have hd₁ : f₁.natDegree > g₁.natDegree := by
      have := scale_degree g
      linarith
    let S₁ : Set ℕ := {p | Nat.Prime p ∧ Exists (Polynomial.map (Int.castRingHom ℚ) (↑p * f₁ + g₁)).IsRoot}
    have hS₁ : S₁.Infinite := by
      refine Set.Infinite.mono ?_ hS
      intro p
      rintro ⟨_,⟨x,hx⟩⟩
      constructor
      assumption
      use x * aₙ
      simp [hfs,hgs]
      field_simp
      simp at hx
      calc _ = ↑aₙ ^ (n - 1)* (↑p * Polynomial.eval x fRat +  Polynomial.eval x gRat) := by ring
        _ = ↑aₙ ^ (n - 1) * 0 := by rw [hx]
        _ = 0 := by ring
    obtain ⟨x,hx⟩ := this hf₁ hg₁ (Polynomial.degree_lt_degree hd₁) hS₁ hfM
    use x / aₙ
    simp [hfs] at hx
    rcases hx with h|h
    · absurd ha
      norm_cast
      exact h.left
    · assumption


/-
We will need the following pigeonhole principle. For a map from an infinite set to a finite set, there must be an element in the image with infinite preimage.
-/
  have lemma_pigeonhole {α β : Type} {s : Set α} (f : α  → β) : s.Infinite → (f '' s).Finite → ∃y : β, { x ∈ s | f x = y}.Infinite := by
    intro hs _
    by_contra h
    simp only [not_exists, Set.not_infinite] at h
    absurd hs
    apply Set.Finite.subset
    show (⋃ y ∈ f '' s, { x ∈ s | f x = y}).Finite
    · apply Set.Finite.biUnion
      assumption
      intro _ _
      apply h
    · intro x hx
      simp
      constructor
      assumption
      use x


-- Since $\operatorname{deg} f>\operatorname{deg} g$, we have $|g(x) / f(x)|<1$ for sufficiently large $x$; more precisely, there is a rational number $R$ such that $|g(x) / f(x)|<1$ for all $x$ with $|x|>R$.

  have lemma_atTop_g_lt_f {f g : Polynomial ℚ} : f.natDegree > g.natDegree → ∃R:ℚ , ∀x:ℚ , x ≥ R → |g.eval x| < |f.eval x| := by
    intro hd
    have hf : f ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hd
    rw [← Filter.eventually_atTop]
    have henz : ∀ᶠ (x:ℚ) in Filter.atTop, f.eval x ≠ 0 := by
      apply f.eventually_no_roots
      exact hf
    have htt := Polynomial.div_tendsto_zero_of_degree_lt g f (Polynomial.degree_lt_degree hd)
    have : (Set.Ioo (-1) 1 : Set ℚ) ∈ nhds 0 := by
      apply Ioo_mem_nhds
      repeat norm_num
    have hes : ∀ᶠ (x:ℚ) in Filter.atTop, -1 < g.eval x / f.eval x ∧ g.eval x / f.eval x < 1 := htt this
    apply Filter.Eventually.mono
    exact Filter.Eventually.and henz hes
    intro x
    rintro ⟨_,_⟩
    rw [← div_lt_one]
    rw [← abs_div]
    rwa [abs_lt]
    rwa [abs_pos]

  have lemma_atInfi_g_lt_f {f g : Polynomial ℚ} : f.natDegree > g.natDegree → ∃R:ℚ , ∀x:ℚ , |x| ≥ R → |g.eval x| < |f.eval x| := by
    intro hd
    let f' := f.comp (- Polynomial.X)
    have hf' : ∀x :ℚ, f.eval x = f'.eval (-x) := by
      simp [f']
    let g' := g.comp (- Polynomial.X)
    have hg' : ∀x :ℚ, g.eval x = g'.eval (-x) := by
      simp [g']
    have hdf : f'.natDegree = f.natDegree := by
      simp [f',Polynomial.natDegree_comp]
    have hdg : g'.natDegree = g.natDegree := by
      simp [g',Polynomial.natDegree_comp]
    have hd' : f'.natDegree > g'.natDegree := by
      rwa [hdf,hdg]
    obtain ⟨R₁,hR₁⟩ := lemma_atTop_g_lt_f hd'
    obtain ⟨R₂,hR₂⟩ := lemma_atTop_g_lt_f hd
    use max R₁ R₂
    intro x
    intro h
    rcases le_abs.mp h with h|h
    · apply hR₂
      linarith [le_max_right R₁ R₂]
    · have :-x ≥ R₁ := by
        linarith [le_max_left R₁ R₂]
      rw [hf' x, hg' x]
      exact hR₁ (-x) this

  -- Introducing the hypotheses.
  replace hd := Polynomial.natDegree_lt_natDegree hg hfg
  set n := f.natDegree with ← hn
  set m := g.natDegree
  have hnn : 0 < n := Nat.zero_lt_of_lt hd
  set fRat := Polynomial.map (Int.castRingHom ℚ) f
  set gRat := Polynomial.map (Int.castRingHom ℚ) g
  have hdRat : fRat.natDegree > gRat.natDegree := by
    repeat rw [Polynomial.natDegree_map_eq_of_injective]
    exact hd
    repeat exact RingHom.injective_int (Int.castRingHom ℚ)

  -- Let's denote r p a root of p f + g if exists.
  let r (p : ℕ) : ℚ :=
    if h : Exists (Polynomial.map (Int.castRingHom ℚ) (↑p * f + g)).IsRoot then Classical.choose h else default
  have hr : ∀ p ∈ S, (Polynomial.map (Int.castRingHom ℚ) (↑p * f + g)).IsRoot (r p) := by
    intro p hp
    simp only [r, dif_pos hp.right]
    exact Classical.choose_spec hp.right

-- Hence all roots of the polynomials $p f+g$ lie in the interval $[-R, R]$.
  obtain ⟨R,hR⟩ := lemma_atInfi_g_lt_f hdRat
  replace hR : ∀ p ∈ S, |r p| < R := by
    intro p hp
    by_contra h
    simp at h
    absurd hR (r p) h
    push_neg
    have : |Polynomial.eval (r p) gRat| = p * |Polynomial.eval (r p) fRat| := by
      have : (p:ℚ) ≥ 0 := Nat.cast_nonneg' p
      rw [← abs_of_nonneg this]
      rw [← abs_mul, abs_eq_abs]
      right
      have := hr p hp
      simp at this
      linarith [this]
    rw [this]
    apply le_mul_of_one_le_left
    · exact abs_nonneg _
    · norm_cast
      exact hp.left.one_le

  have hd' (p : ℕ) : (p * f + g).natDegree ≤ n := by
    apply Polynomial.natDegree_add_le_of_degree_le
    rw [mul_comm]
    apply Polynomial.natDegree_mul_C_le f (p:ℤ)
    linarith

-- The leading coefficient of $p f+g$ is $p$, and if $r=u / v$ is a rational root of $p f+g$ with $(u, v)=1$ and $v>0$, then either $v=1$ or $v=p$.

  replace huv : ∀ p ∈ S, (p * f + g).sum (fun k a => a * (r p).den^(n-k) * (r p).num^k ) = 0 := by
    intro p hp
    set u := (r p).num
    set v := (r p).den
    have hv : (v:ℚ) ≠ 0 := by
      norm_cast
      simp [v]
    have : (p * f + g).sum (fun k a => a * v^(n-k) * u^k ) = v^n * (Polynomial.eval (r p) (Polynomial.map (Int.castRingHom ℚ) (p * f + g))) := by
      simp only [Polynomial.eval_map,Polynomial.eval₂,Polynomial.sum, Finset.mul_sum]
      push_cast
      apply Finset.sum_congr
      trivial
      intro k hk
      apply Polynomial.le_natDegree_of_mem_supp at hk
      replace hk := le_trans hk (hd' p)
      rw [pow_sub₀ (v:ℚ) hv hk]
      have : (u:ℚ) = (v:ℚ) * r p := by
        simp [u,v]
      rw [this]
      field_simp
      ring
    qify
    rw [this]
    simp only [mul_eq_zero]
    right
    exact hr p hp

  -- The denominator of r p is either 1 or p.
  have hdicho : ∀ p ∈ S, (r p).den = 1 ∨ (r p).den = p := by
    peel huv with p hp huv
    zify
    set u := (r p).num
    set v : ℕ := (r p).den
    suffices v ∣ p by
      simp [v] at this ⊢
      rwa [← Nat.dvd_prime hp.left]
    rw [← f.eraseLead_add_monomial_natDegree_leadingCoeff, hM, hn, mul_add, add_comm (_ * _), add_assoc] at huv
    rw [Polynomial.sum_add_index] at huv
    have : p = Polynomial.C (p:ℤ) := rfl
    conv at huv =>
      arg 1
      arg 1
      rw [this]
      simp only [Polynomial.C_mul_monomial]
      simp
    have : (v:ℤ) ∣ p * u ^ n + (p * f.eraseLead + g).sum (fun k a => a * v ^ (n - k) * u ^ k) := by
      rw [huv]
      simp
    have : (v:ℤ) ∣ p * u^n := by
      rw [Int.dvd_iff_dvd_of_dvd_add this]
      apply Finset.dvd_sum
      intro k hk
      dsimp
      apply dvd_mul_of_dvd_left
      apply dvd_mul_of_dvd_right
      apply dvd_pow_self
      rw [Nat.sub_ne_zero_iff_lt]
      apply Nat.lt_of_le_pred
      exact hnn
      apply le_trans
      exact Polynomial.le_natDegree_of_mem_supp k hk
      apply Polynomial.natDegree_add_le_of_degree_le
      apply le_trans
      apply Polynomial.natDegree_C_mul_le
      apply Polynomial.eraseLead_natDegree_le
      apply Nat.le_pred_of_lt
      exact hd
    simp [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_pow] at this
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ this
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm]
    exact (r p).reduced
    · simp
    · intro k a b
      ring

  let S₁ := { p ∈ S | (r p).den = 1 }
  let S₂ := { p ∈ S | (r p).den = p }
  replace hdicho : (S₁ ∪ S₂).Infinite := by
    convert hS
    ext p
    constructor
    · rintro (h|h) <;> exact h.left
    · intro h
      rcases hdicho p h with (j|j)
      left; exact ⟨h,j⟩
      right; exact ⟨h,j⟩

  rcases Set.infinite_union.mp hdicho with hS|hS

  -- First consider the case when $v=1$ infinitely many times. If $v=1$ then $|u| \leq R$, so there are only finitely many possibilities for the integer $u$. Therefore there exist distinct primes $p$ and $q$ for which we have the same value of $u$. Then the polynomials $p f+g$ and $q f+g$ share this root, implying $f(u)=g(u)=0$. So in this case $f$ and $g$ have an integer root in common.

  · obtain ⟨x,hx⟩ : ∃ x : ℚ, { p ∈ S₁| r p = x}.Infinite := by
      apply lemma_pigeonhole r hS
      obtain ⟨K,hK⟩ := exists_nat_ge R
      apply Set.Finite.subset
      show (Set.iUnion (fun (k:Finset.range K) => {x ∈ r '' S₁ | x.num.natAbs = (k:ℕ)})).Finite
      · apply Set.finite_iUnion
        simp
        intro k _
        apply Set.Finite.subset
        show Set.Finite {(k:ℚ), -(k:ℚ)}
        · simp
        intro x
        simp
        intro p hp hpx
        have hxn : x.den = 1 := by
          rw [← hpx]
          exact hp.right
        intro
        rw [← (Rat.den_eq_one_iff x).mp hxn]
        norm_cast
        rwa [← Int.natAbs_eq_iff]
      simp
      intro p hp
      simp
      constructor
      use p
      qify
      rw [(Rat.den_eq_one_iff (r p)).mp hp.right]
      apply lt_of_lt_of_le (hR p hp.left)
      exact hK
    replace hx : {q : ℚ | q * fRat.eval x + gRat.eval x = 0}.Infinite := by
      apply Set.Infinite.mono
      show Nat.cast '' { p ∈ S₁ | r p = x} ⊆ _
      · simp
        intro p hp _ hpx
        have := hr p hp
        simp [hpx] at this
        exact this
      · rwa [Set.infinite_image_iff]
        intro p _ p' _
        norm_cast
        exact id
    let l : Polynomial ℚ := Polynomial.monomial 1 (fRat.eval x) + Polynomial.C (gRat.eval x)
    have hl : fRat.eval x = l.coeff 1 := by
      simp [l, Polynomial.coeff_monomial]
    replace hx : { q : ℚ | l.IsRoot q }.Infinite := by
      apply Set.Infinite.mono
      show {q : ℚ | q * fRat.eval x + gRat.eval x = 0} ⊆ _
      · simp
        intro q hq
        simp [l]
        rw [← hq]
        ring
      · exact hx
    have := Polynomial.eq_zero_of_infinite_isRoot l hx
    use x
    simp [hl, this]

  -- Now suppose that $v=p$ infinitely many times. By comparing the exponent of $p$ in the denominators of $p f(u / p)$ and $g(u / p)$ we get $m=n-1$ and $p f(u / p)+g(u / p)=0$ reduces to an equation of the form  $$ \left(u^{n}+a_{n-1} p u^{n-1}+\ldots+a_{0} p^{n}\right)+\left(b_{n-1} u^{n-1}+b_{n-2} p u^{n-2}+\ldots+b_{0} p^{n-1}\right)=0 . $$  The equation above implies that $u^{n}+b_{n-1} u^{n-1}$ is divisible by $p$ and hence, since $(u, p)=1$, we have $u+b_{n-1}=p y$ with some integer $y$.

  · obtain ⟨l, hl⟩ := Nat.exists_eq_succ_of_ne_zero hnn.ne.symm
    replace huv : ∀ p ∈ S₂, ((p * f + g).sum fun k a ↦ a * p ^ (n - k) * (r p).num ^ k) = 0 := by
      intro p hp
      have := huv p hp.left
      rwa [hp.right] at this
    replace huv : ∀ p ∈ S₂, (p : ℤ) ∣ (g.coeff l + (r p).num) := by
      peel huv with p hp huv
      set u := (r p).num
      rw [Polynomial.sum_over_range' _ (by simp) (n+1) (Nat.lt_succ.mpr (hd' p))] at huv
      have := by
        calc
        _ = ∑ k ∈ Finset.range (n + 1), (p * f + g).coeff k * p ^ (n - k) * u ^ k := by rw [huv]
        _ = ∑ k ∈ Finset.range n, (p * f + g).coeff k * p ^ (n - k) * u ^ k +  p * u ^ n := by simp [Finset.sum_range_succ]; left; simp [Polynomial.coeff_eq_zero_of_natDegree_lt hd,n,hM]
        _ = ∑ k ∈ Finset.range l, (p * f + g).coeff k * p ^ (n - k) * u ^ k + (p * f + g).coeff l * p * u ^ l +  p * u ^ n := by rw [hl]; simp [Finset.sum_range_succ]
        _ = (∑ k ∈ Finset.range l, (p * f + g).coeff k * p ^ (n - k) * u ^ k + p ^ 2 * f.coeff l * u ^ l) + p * ((g.coeff l + u) * u ^ l) := by simp [hl]; ring
      have : (p:ℤ)^2 ∣ (∑ k ∈ Finset.range l, (p * f + g).coeff k * p ^ (n - k) * u ^ k + p ^ 2 * f.coeff l * u ^ l) + p * ((g.coeff l + u) * u ^ l) := by
        rw [← this]
        simp
      have : (p:ℤ)^2 ∣ p * ((g.coeff l + u) * (u ^ l)) := by
        rw [← Int.dvd_iff_dvd_of_dvd_add this]
        apply dvd_add
        · apply Finset.dvd_sum
          intro k hk
          apply dvd_mul_of_dvd_left
          apply dvd_mul_of_dvd_right
          apply pow_dvd_pow
          simp at hk
          simp [hl]
          · apply Nat.le_sub_of_add_le
            rw [add_comm]
            apply Nat.succ_le_succ
            exact hk
        · repeat apply dvd_mul_of_dvd_left
          apply dvd_refl

      rw [pow_two, mul_dvd_mul_iff_left (by norm_cast; exact hp.left.left.ne_zero : (p:ℤ) ≠ 0)] at this
      simp [← Int.natAbs_dvd_natAbs, Int.natAbs_mul, Int.natAbs_pow] at this ⊢
      refine Nat.Coprime.dvd_of_dvd_mul_right ?_ this
      apply Nat.Coprime.pow_right
      rw [← hp.right]
      simpa [u,Nat.coprime_comm] using (r p).reduced
    replace huv : ∀ p ∈ S₂, ((g.coeff l) / p + r p).num = (g.coeff l) / p + r p := by
      intro p hp
      obtain ⟨k,hk⟩ := huv p hp
      replace hk : (g.coeff l) / p + r p = k :=
        calc
          (g.coeff l) / p + r p  = (g.coeff l) / p + (r p).num / (r p).den := by rw [Rat.num_div_den (r p)]
          _ = ((g.coeff l) + (r p).num) / p := by simp [hp.right]; ring
          _ = p * k / p:= by qify at hk; rw [hk]
          _ = k := by rw [mul_div_cancel_left₀]; norm_cast;exact hp.left.left.ne_zero
      rw [hk]
      rfl

    -- On the other hand all roots of $p f+g$ lie in the interval $[-R, R]$, so the integer $y$ can attain only finitely many values. Hence there exists an integer $k$ such that the number $\frac{p y-b_{n-1}}{p}=y-\frac{b_{n-1}}{p}$ is a root of $p f+g$ for infinitely many primes $p$.

    obtain ⟨y,hy⟩ : ∃ y : ℚ,  { p ∈ S₂ | (g.coeff l)/ p + r p = y }.Infinite := by
      apply lemma_pigeonhole (fun p => (g.coeff l)/ p + r p)
      · exact hS
      · apply Set.Finite.of_finite_image
        show ((fun x => x.num) '' _).Finite
        · simp [Set.image]
          obtain ⟨K,hK⟩ := exists_nat_gt R
          apply Set.Finite.subset (Set.finite_Icc (-(|g.coeff l| + K):ℤ) (|g.coeff l| + K:ℤ))
          simp [Set.Icc, - neg_add_rev, - add_neg_le_iff_le_add]
          intro p hp
          qify
          rw [huv p hp]
          rw [← abs_le]
          apply le_trans
          exact abs_add _ _
          apply add_le_add
          · rw [abs_div]
            refine div_le_self (abs_nonneg _) ?_
            norm_cast
            exact hp.left.left.one_le
          · linarith [hR p hp.left]
        · simp [Set.InjOn]
          intro p hp p' hp' h
          qify at h
          rwa [huv p hp, huv p' hp'] at h
    use y
    replace hr : ∀ p ∈ S, (Polynomial.eval (r p) fRat) + (p:ℚ)⁻¹ * (Polynomial.eval (r p) gRat) = 0 := by
      peel hr with p hp hr
      have hpn : (p:ℚ) ≠ 0 := by
        norm_cast
        exact hp.left.ne_zero
      rw [← mul_right_inj' hpn]
      ring_nf
      rw [mul_inv_cancel₀ hpn]
      simp
      simp at hr
      exact hr
    set S₃ := { p ∈ S₂ | (g.coeff l) / (p:ℚ) + r p = y }
    replace hS : S₃.Infinite := hy

    -- For these primes we have  $$ f\left(y-b_{n-1} \frac{1}{p}\right)+\frac{1}{p} g\left(y-b_{n-1} \frac{1}{p}\right)=0.$$  Letting $p → +\infty$, we find that $y$ is a root of $f$.

    replace hy : Filter.Tendsto r (Filter.atTop ⊓ Filter.principal S₃) (nhds y) := by
      apply Filter.Tendsto.congr'
      show Filter.EventuallyEq _ (fun p:ℕ ↦ y - (g.coeff l :ℚ)/ (p:ℚ)) r
      · apply Filter.eventuallyEq_of_mem
        exact Filter.mem_inf_of_right <| Filter.mem_principal_self S₃
        intro p hp
        simp
        linarith [hp.right]
      conv in nhds y => rw [← sub_zero y]
      apply Filter.Tendsto.sub
      exact tendsto_const_nhds
      refine Filter.Tendsto.mono_left ?_ inf_le_left
      rw [← mul_zero (g.coeff l : ℚ)]
      conv in (fun (_:ℕ) ↦ _ ) =>
        ring_nf
      apply Filter.Tendsto.const_mul (g.coeff l : ℚ)
      exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have _ : Filter.Tendsto (fun (p:ℕ) => Polynomial.eval (r p) fRat + (p:ℚ)⁻¹ * Polynomial.eval (r p) gRat) (Filter.atTop ⊓ Filter.principal S₃) (nhds <| Polynomial.eval y fRat) := by
      rw [← add_zero <| Polynomial.eval y fRat]
      apply Filter.Tendsto.add
      · exact Filter.Tendsto.comp (Polynomial.continuousAt fRat) hy
      rw [← zero_mul <| Polynomial.eval y gRat]
      apply Filter.Tendsto.mul
      · refine tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp ?_)
        simp [← Function.id_def, Filter.tendsto_id']
      · exact Filter.Tendsto.comp (Polynomial.continuousAt gRat) hy
    have _ : Filter.Tendsto (fun (p:ℕ) => Polynomial.eval (r p) fRat + (p:ℚ)⁻¹ * Polynomial.eval (r p) gRat) (Filter.atTop ⊓ Filter.principal S₃) (nhds 0) := by
      refine Filter.Tendsto.congr' (?_ : (fun (_:ℕ) ↦ (0:ℚ)) =ᶠ[_] _) tendsto_const_nhds
      · simp [Filter.EventuallyEq, Filter.Eventually]
        apply Filter.mem_inf_of_right
        simp
        intro p hp
        exact (hr p hp.left.left).symm
    apply tendsto_nhds_unique'
    show Filter.NeBot (Filter.atTop ⊓ Filter.principal S₃)
    · rw [← Nat.cofinite_eq_atTop]
      exact hS.cofinite_inf_principal_neBot
    repeat assumption
  --In summary the monic polynomial $f$ obtained after the initial reduction always has an integer root. Therefore the original polynomial $f$ has a rational root.
