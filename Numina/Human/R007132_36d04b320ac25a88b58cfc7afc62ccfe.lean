import Mathlib

open Polynomial

/- For how many ordered pairs $(a,b)$ of integers does the polynomial $x^3+ax^2+bx+6$ have $3$ distinct integer roots?
$\textbf{(A)}\ 5 \qquad\textbf{(B)}\ 6 \qquad\textbf{(C)}\ 8 \qquad\textbf{(D)}\ 7 \qquad\textbf{(E)}\ 4$ -/
theorem algebra_95828 :
    {(a, b) : ℤ × ℤ | ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ x^3 + a * x^2 + b * x + 6 = 0 ∧
      y^3 + a * y^2 + b * y + 6 = 0 ∧ z^3 + a * z^2 + b * z + 6 = 0}.ncard = 5 := by
  set s := {(a, b) : ℤ × ℤ | _}
  -- it is enough to show that all possible values of (a, b) are in the following set
  suffices s = {(6, 11), (0, -7), (-2, -5), (-4, 1), (-6, -1)} by rw [this]; norm_num
  ext ⟨a, b⟩
  simp only [Set.mem_setOf_eq, Int.reduceNeg, Set.mem_insert_iff,
    Prod.mk.injEq, Set.mem_singleton_iff, s]
  constructor
  · intro ⟨x, y, z, hxy, hyz, hzx, hx0, hy0, hz0⟩
    -- let x, y, z be distinct integer roots of X ^ 3 + a * X ^ 2 + b * X + 6
    -- we want to find all possible values of (a, b)
    -- without loss of generality, assume that x < y < z
    wlog h : x < y ∧ y < z generalizing x y z with h1
    · by_cases h2 : x < y
      · simp [h2] at h
        by_cases h3 : x < z
        · exact h1 x z y hzx.symm hyz.symm hxy.symm hx0 hz0 hy0 (by omega)
        · exact h1 z x y hzx hxy hyz hz0 hx0 hy0 (by omega)
      · by_cases h3 : y < z
        · by_cases h4 : x < z
          · exact h1 y x z hxy.symm hzx.symm hyz.symm hy0 hx0 hz0 (by omega)
          · exact h1 y z x hyz hzx hxy hy0 hz0 hx0 (by omega)
        · exact h1 z y x hyz.symm hxy.symm hzx.symm hz0 hy0 hx0 (by omega)
    -- let p be the polynomial X ^ 3 + a * X ^ 2 + b * X + 6
    set p : Polynomial ℝ := X ^ 3 + C (a : ℝ) * X ^ 2 + C (b : ℝ) * X + (C 6)
    have hp_deg : p.natDegree = 3 := by dsimp [p]; compute_degree!
    have hp0 : p ≠ 0 := Polynomial.ne_zero_of_natDegree_gt (by omega : 0 < p.natDegree)
    have hp_monic : p.Monic := by
      simp_rw [Monic, leadingCoeff, hp_deg, p]
      compute_degree!
    -- roots of p are x, y, z
    have hp_roots : p.roots = {↑x, ↑y, ↑z} := by
      refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ ?_)
      · refine (Multiset.le_iff_subset ?_).mpr ?_
        · simp
          omega
        · simp [hp0]
          rify at hx0 hy0 hz0
          simp [p, hx0, hy0, hz0]
      · simp
        exact le_trans (Polynomial.card_roots' _) (by omega)
    -- use Vieta's identities and get
    -- a = -(x + y + z)
    -- b = x * y + x * z + y * z
    -- x * y * z = -6
    have ⟨ha, hb, eq⟩ : a = -(x + y + z) ∧ b = x * y + x * z + y * z ∧ x * y * z = -6 := by
      let p3 : Cubic ℝ := { a := 1, b := a, c := b, d := 6 }
      have p3_eq : p3.toPoly = p := by simp [Cubic.toPoly, p]
      have hroots : (Cubic.map (RingHom.id ℝ) p3).roots = {↑x, ↑y, ↑z} := by
        simp [Cubic.map_roots, p3_eq, hp_roots]
      have h := Cubic.eq_sum_three_roots (by norm_num) hroots
      simp [Cubic.map] at h
      rify
      simp [h.1, h.2.1, h.2.2]
    clear * - h eq ha hb
    -- we need to solve the equation x * y * z = -6 over integers x < y < z
    have heq1 (x y z : ℤ) (h : x * y * z = -6) : z.natAbs = 1 ∨ z.natAbs = 2 ∨ z.natAbs = 3 ∨ z.natAbs = 6 := by
      apply_fun Int.natAbs at h
      simp [Int.natAbs_mul] at h
      have : z.natAbs ∈ (6).divisors := by simp; use x.natAbs * y.natAbs; linear_combination -h
      simp [show (6 : ℕ).divisors = {1, 2, 3, 6} from rfl] at this
      exact this
    have heq_neg (x y z : ℤ) (h : x * y * z = -6) (hz : z < 0) : z = -6 ∨ z = -3 ∨ z = -2 ∨ z = -1 := by
      have := heq1 x y z h
      omega
    have heq_pos (x y z : ℤ) (h : x * y * z = -6) (hz : 0 < z) : z = 6 ∨ z = 3 ∨ z = 2 ∨ z = 1 := by
      have := heq1 x y z h
      omega
    have ineq : x * y * z < 0 := by linarith
    rw [mul_neg_iff] at ineq
    -- consider two cases: 0 < x * y ∧ z < 0 and x * y < 0 ∧ 0 < z
    rcases ineq with ⟨hxy, hz⟩ | ⟨hxy, hz⟩
    · rw [mul_pos_iff] at hxy
      -- if 0 < x * y ∧ z < 0 then x < 0 and y < 0 (since x < y < z)
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · omega
      -- consider all possible values of z and x and find that (x, y, z) = (-3, -2, -1)
      · rcases heq_neg x y z eq hz with hz | hz | hz | hz <;> subst z <;> try nlinarith
        rcases heq_neg y (-1) x (show y * (-1) * x = -6 by linarith) hx with hx | hx | hx | hx <;> subst x <;> try linarith
        omega
    · rw [mul_neg_iff] at hxy
      -- if x * y < 0 < z then x < 0, 0 < y, 0 < z (since x < y < z)
      rcases hxy with ⟨hx, hy⟩ | ⟨hx, hy⟩
      · linarith
      · replace hy := heq_pos x z y (by linarith) hy
        -- consider all possible values of z and y and find 4 other solutions
        rcases heq_pos x y z eq hz with hz | hz | hz | hz <;> subst z <;> try nlinarith
        all_goals {
          rcases hy with hy | hy | hy | hy <;> subst y <;> try nlinarith
          all_goals omega
        }
  · intro h
    -- it is left to check that the given values of (a, b) satisfy all conditions
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · use -3, -2, -1; norm_num
    · use -3, 1, 2; norm_num
    · use -2, 1, 3; norm_num
    · use -1, 2, 3; norm_num
    · use -1, 1, 6; norm_num