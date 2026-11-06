import Mathlib

/- Soient $\left(a_{n}\right)_{n \geqslant 1}$ une suite croissante d'entiers strictement positifs et $k$ un entier strictement positif. Supposons que pour un certain $r \geqslant 1$, on $a \frac{r}{a_{r}}=k+1$. Montrer qu'il existe un entier $s \geqslant 1$ tel que $\frac{s}{a_{s}}=k$. -/
theorem number_theory_607710 (a : ℕ+ → ℤ) (ha : StrictMono a)
    (ha1 : ∀ n, 0 < a n) (k : ℤ) (hk : 0 < k)
    (h : ∃ r, 1 ≤ r ∧ (r / a r : ℚ) = k + 1) :
    ∃ s, 1 ≤ s ∧ (s / a s : ℚ) = k := by
  -- Soit $v\_{n}=\mathrm{n}-\mathrm{ka}*{\mathrm{n}}$ pour tout $\mathrm{n} \geqslant 1$.
  obtain ⟨v, hv⟩ := show ∃v : ℕ+ → ℤ, v = fun n ↦ n - k * a n by simp
  -- Le problème revient à montrer qu'il existe $s$ tel que $v*{s}=0$.
  suffices ∃ s, 1 ≤ s ∧ v s = 0 by
    obtain ⟨s, hs₁, hs₂⟩ := this
    use s
    use hs₁
    rw [hv] at hs₂; simp at hs₂
    rw [div_eq_iff_mul_eq]
    norm_cast
    exact Eq.symm (Int.eq_of_sub_eq_zero hs₂)
    simp; linarith [ha1 s]
  -- On observe que $\nu\_{1}=1-k a\_{1} \leqslant 0$,
  have hv₁ : v 1 ≤ 0 := by
    rw [hv]; simp
    exact one_le_mul_of_one_le_of_one_le hk (ha1 1)
  -- que $\nu\_{r}=r-k a\_{r}=a\_{r}&gt;0$
  obtain ⟨r, hr₁, hr₂⟩ := h
  have hvᵣ : v r > 0 := by
    rw [hv]; simp
    rw [div_eq_iff_mul_eq] at hr₂
    norm_cast at hr₂
    rw [←hr₂]
    apply Int.mul_lt_mul_of_pos_right ?_ (ha1 r)
    repeat simp
    linarith [ha1 r]
  -- et qu'enfin $\nu\_{n+1}=$ $(n+1)-k a\_{n+1}=n-k a\_{n+1}+1 \leqslant n-k a\_{n}+1=v\_{n}+1$, car la suite $\left(a\_{n}\right)*{n}$ est croissante.
  have hvₙ (n : ℕ+) : v (n + 1) ≤ v n + 1 := by
    rw [hv]
    simp
    have h : 1 ≤ k * (a (n + 1) - a n) + 1 := by
      simp
      apply Int.mul_nonneg (Int.le_of_lt hk)
      apply Int.sub_nonneg_of_le (Int.le_of_lt (ha ?_))
      exact PNat.lt_add_right n 1
    apply Int.add_le_of_le_sub_left
    ring_nf
    linarith
  -- Intuitivement, on a donc une suite d'entiers qui part d'un nombre négatif, atteint un nombre strictement positif, et ne peut augmenter que d'au plus 1 à chaque fois : elle doit atteindre 0.
  -- Prouvons-le : soit $s$ le plus grand entier inférieur à $r$ tel que $v*{s} \leqslant 0$ (il existe car $\nu\_{1} \leqslant 0$ ).
  have : ∃s, IsGreatest {n : ℕ+ | v n ≤ 0 ∧ n < r} s := by
    -- Prove that, {n : ℕ+ | v n ≤ 0 ∧ n < r} has upper bound.
    apply BddAbove.exists_isGreatest_of_nonempty
    apply bddAbove_def.mpr
    use r
    simp
    intro y hy₁ hy₂
    exact le_of_lt hy₂
    -- Prove that, {n : ℕ+ | v n ≤ 0 ∧ n < r} is nonempty.
    apply Set.nonempty_of_mem
    case hS'.x => exact 1
    simp
    refine ⟨hv₁, ?_⟩
    apply lt_of_le_of_ne hr₁
    intro hr'
    rw [hr'] at hv₁
    linarith
  -- Alors, comme $v\_{r}&gt;0$, on a $s0$.
  obtain ⟨s, hs₁, hs₂⟩ := this
  use s; simp
  have ⟨hs₃, hs₄⟩ := hs₁
  have : v (s + 1) > 0 := by
    by_cases h: s + 1 = r
    · rw [h]; assumption
    have h : s + 1 < r := by apply lt_of_le_of_ne hs₄ h
    by_contra! hs₀
    unfold upperBounds at hs₂
    simp at hs₂
    specialize hs₂ hs₀ h
    absurd hs₂
    simp [PNat.lt_add_right s 1]
  -- On a donc $v\_{s+1} \geqslant 1$, donc $0 \geqslant v\_{s} \geqslant v\_{s+1}-1 \geqslant 0$, donc $v\_{s}=0$, de sorte que $\frac{s}{a\_{s}}=k$.
  have : 1 ≤ v (s + 1) := by omega
  linarith [le_trans this (hvₙ s)]
