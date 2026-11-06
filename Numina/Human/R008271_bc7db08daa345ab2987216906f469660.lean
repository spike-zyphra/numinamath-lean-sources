import Mathlib

open Polynomial

/- 5-141 Find all non-zero polynomials $f(x)=a_{0}+a_{1} x+\cdots+a_{n} x^{n}$ that satisfy the equation $f\left(x^{2}\right)=(f(x))^{2}$, where $x$ is a real number. -/
theorem algebra_250655 {f : Polynomial ℝ} (hf : f ≠ 0) :
    (∀ x, f.eval (x ^ 2) = (f.eval x) ^ 2) ↔ ∃ n, f = X ^ n := by
  constructor
  -- show that f(x ^ 2) = f(x) ^ 2 implies that f = X ^ n for some n
  · intro h
    set n := f.natDegree with hn
    -- let n be the degree of f and prove that f = X ^ n
    use n
    -- we have a polynomial equality f ^ 2 = f(X ^ 2)
    have heq : f ^ 2 = f.comp (X ^ 2) := by
      apply Polynomial.funext
      intro x
      simp [h]
    -- show that the leading coefficient (call it a0) of f is 1
    have hf_leading : f.leadingCoeff = 1 := by
      -- the leading coefficient of f ^ 2 is a0 ^ 2
      have hp : (f ^ 2).leadingCoeff = f.leadingCoeff ^ 2 := by simp only [leadingCoeff_pow]
      -- the leading coefficient of f(X ^ 2) is a0
      have hq : (f.comp (X ^ 2)).leadingCoeff = f.leadingCoeff := by simp [leadingCoeff_comp]
      -- we get a0 * (a0 - 1) = 0
      replace eq : f.leadingCoeff * (f.leadingCoeff - 1) = 0 := by
        rw [heq] at hp
        linear_combination hq - hp
      -- so a0 = 0 or a0 = 1
      -- if a0 = 0 then f = 0, a contradiction, so a0 = 1
      rw [mul_eq_zero] at eq
      cases eq with
      | inl h => rw [leadingCoeff_eq_zero] at h; contradiction
      | inr h => linarith
    -- consider two cases: n = 0 and 0 < n
    by_cases hn0 : n = 0
    · rw [hn0, pow_zero]
      -- if n = 0 then f.leadingCoeff = 1 implies that f = 1
      rw [← Monic.natDegree_eq_zero hf_leading]
      exact hn0
    -- let g be the polynomial f as a polynomial over ℂ
    set g := f.map Complex.ofRealHom
    -- g satisfies the same polynomial equality as f
    have hg : g ^ 2 = g.comp (X ^ 2) := by
      apply_fun Polynomial.map Complex.ofRealHom at heq
      simp at heq
      simp [g, heq, Polynomial.map_comp]
    have hg_eval z : eval z g ^ 2 = eval (z ^ 2) g := by
      apply_fun Polynomial.eval z at hg
      simp at hg
      exact hg
    have hg_deg : g.natDegree = n := by simp only [natDegree_map, g]
    have hg_leading : g.leadingCoeff = 1 := by simp [g, hf_leading]
    have hg0 : g ≠ 0 := by simp [g, hf]
    -- show that 0 is the only root of g
    have hg_roots : g.roots = n • {0} := by
      -- g has exactly n roots (because g ∈ ℂ[X] and the degree of g is n)
      have n_eq : n = g.roots.card := by
        symm
        rw [←hg_deg, ←Polynomial.splits_iff_card_roots]
        exact IsAlgClosed.splits g
      rw [Multiset.nsmul_singleton, n_eq]
      apply Multiset.eq_replicate_of_mem
      -- it is enough to show that z ∈ g.roots implies that z = 0
      simp_rw [Polynomial.mem_roots hg0]
      intro z hz
      -- suppose that z ∈ g.roots and z ≠ 0
      -- show that g = 0 in this case
      contrapose! hg0
      -- we have g(u ^ 2 ^ n) = g(u) ^ (2 ^ n) for any natural n and complex u
      have hzn z n : g.eval (z ^ 2 ^ n) = (g.eval z) ^ (2 ^ n) := by
        induction n with
        | zero => simp only [pow_zero, pow_one]
        | succ n ih => rw [Nat.pow_add, pow_mul, pow_one, ←hg_eval, ih, pow_mul]
      -- show that roots of X ^ (2 ^ n) - z are also roots of g
      -- and that X ^ (2 ^ n) - z has more than n roots
      -- it follows that g has more than n roots, so g = 0
      apply eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (nthRoots (2 ^ n) z).toFinset
      · simp
        -- if v is a root of X ^ (2 ^ n) - z then
        -- v ^ (2 ^ n) = z and we have
        -- 0 = g(z) = g(v ^ (2 ^ n)) = g(v) ^ (2 ^ n)
        intro v eq
        replace hzn := hzn v n
        rw [eq, hz, eq_comm] at hzn
        rw [pow_eq_zero_iff (by norm_num)] at hzn
        exact hzn
      · have hp := Complex.isPrimitiveRoot_exp (2 ^ n) (by norm_num)
        have : (nthRoots (2 ^ n) z).Nodup := IsPrimitiveRoot.nthRoots_nodup hp hg0
        -- show that there are exactly 2 ^ n roots of X ^ (2 ^ n) - z
        rw [Multiset.toFinset_card_of_nodup this]
        have : ∃ v, v ^ (2 ^ n) = z := by
          use z ^ ((↑((2 : ℕ) ^ n) : Complex)⁻¹)
          rw [Complex.cpow_nat_inv_pow]
          norm_num
        simp [IsPrimitiveRoot.card_nthRoots hp, this, hg_deg]
        clear * -
        -- it is left to show that n < 2 ^ n for all n
        induction n with
        | zero => norm_num
        | succ n ih =>
          rw [pow_add, pow_one, mul_two]
          exact add_lt_add_of_lt_of_le ih (by omega)
    -- we can write g = ∏ a ∈ g.roots, (X - a) = X ^ n (since g.roots = n • {0})
    have hg_eq := Polynomial.eq_prod_roots_of_monic_of_splits_id hg_leading (IsAlgClosed.splits g)
    simp [hg_roots, Multiset.map_nsmul, Multiset.prod_nsmul] at hg_eq
    -- it is left to show that f = X ^ n
    -- show that f(x) = (X ^ n)(x) for all real x
    apply Polynomial.funext
    intro x
    rw [←Complex.ofReal_inj]
    -- we have f(x) = g(x) for all real x
    have hgf x : f.eval x = g.eval (x : ℂ) := by
      simp_rw [g, eval_map, eval_eq_sum, eval₂_def, sum_def]
      simp
    -- g(x) = x ^ n so f(x) = x ^ n for all real x and it follows that f = X ^ n
    simp_all only [eval_pow, eval_X, Complex.ofReal_pow]
  · intro ⟨n, eq⟩ x
    -- show that f = X ^ n satisfies the equality f(x ^ 2) = f(x) ^ 2
    simp [eq, ←pow_mul, mul_comm]