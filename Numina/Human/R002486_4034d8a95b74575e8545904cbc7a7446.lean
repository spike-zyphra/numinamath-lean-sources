import Mathlib

open Polynomial

/- For how many values of the constant $k$ will the polynomial $x^{2}+kx+36$ have two distinct integer roots?
$\textbf{(A)}\ 6 \qquad\textbf{(B)}\ 8 \qquad\textbf{(C)}\ 9 \qquad\textbf{(D)}\ 14 \qquad\textbf{(E)}\ 16$ -/
theorem algebra_94130 :
    Set.ncard {k : ℤ | ∃ x y : ℤ, x ≠ y ∧ x^2 + k * x + 36 = 0 ∧ y^2 + k * y + 36 = 0} = 8 := by
  set s := {k : ℤ | _}
  -- show that all possible values of k are -37, 37, -20, 20, -15, 15, -13, 13
  suffices s = {-37, 37, -20, 20, -15, 15, -13, 13} by rw [this]; norm_num
  ext k
  simp [s]
  constructor
  · intro ⟨x, y, hxy, hx, hy⟩
    set p : Polynomial ℤ := X ^ 2 + C k * X + C 36
    -- suppose that x and y are distinct and p.eval x = 0 and p.eval y = 0
    have pdeg : p.natDegree = 2 := by dsimp [p]; compute_degree!
    have p0 : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < p.natDegree)
    have p2 : p.leadingCoeff = 1 := by
      rw [leadingCoeff, pdeg]
      simp [p]
      compute_degree
    -- prove that p.roots = {x, y}
    have hr : p.roots = {x, y} := by
      refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ ?_)
      · refine (Multiset.le_iff_subset ?_).mpr ?_
        · simp [hxy]
        · simp [p0]
          simp [p, hx, hy]
      · simp
        exact le_trans (Polynomial.card_roots' _) (by omega)
    have hr2 : p.roots.card = p.natDegree := by simp [hr, pdeg]
    -- use Vieta's formula to compute k = -(x + y)
    have eq1 : k = -(x + y) := calc
      k = p.coeff 1 := by simp [p]
      _ = -(x + y) := by
        rw [coeff_eq_esymm_roots_of_card hr2 (by omega), p2, pdeg, hr]
        simp [Multiset.esymm, Multiset.powersetCard_one]
        ring
    -- use Vieta's formula to compute 36 = x * y
    have eq2 : 36 = x * y := calc
      36 = p.coeff 0 := by simp [p]
      _ = x * y := by
        rw [coeff_eq_esymm_roots_of_card hr2 (by omega), p2, pdeg, hr]
        simp [Multiset.esymm, Multiset.powersetCard_one]
    have hx0 : x ≠ 0 := by contrapose! eq2; rw [eq2]; norm_num
    -- we get that |x| is a divisor of 36 and x * x ≠ 36 (because x ≠ y)
    replace ⟨hxx, hx⟩ : x * x ≠ 36 ∧ x.natAbs ∈ (36).divisors := by
      constructor
      · rw [eq2]
        contrapose! hxy
        exact Int.eq_of_mul_eq_mul_left hx0 hxy
      · simp
        use y.natAbs
        apply_fun Int.natAbs at eq2
        rw [Int.natAbs_mul] at eq2
        omega
    -- list all divisors of 36
    rw [show (36 : ℕ).divisors = {1, 2, 3, 4, 6, 9, 12, 18, 36} by rfl] at hx
    simp at hx
    rw [eq1]
    replace eq2 : y = 36 / x := by
      symm
      apply Int.ediv_eq_of_eq_mul_left (by omega)
      rw [eq2, mul_comm]
    -- consider all possible values of |x| and compute corresponding values of k
    rcases hx with h | h | h | h | h | h | h | h | h
    all_goals {
      simp only [Int.natAbs_eq_iff] at h
      cases' h with h h <;> subst h eq2 <;> norm_num at hxx ⊢
    }
  · intro h
    -- show that for any choice of k we can find x ≠ y such that
    -- x and y are roots of X ^ 2 + k * X + 36
    rcases h with h | h | h | h | h | h | h | h <;> rw [h]
    · use 1, 36; norm_num
    · use -1, -36; norm_num
    · use 2, 18; norm_num
    · use -2, -18; norm_num
    · use 3, 12; norm_num
    · use -3, -12; norm_num
    · use 4, 9; norm_num
    · use -4, -9; norm_num