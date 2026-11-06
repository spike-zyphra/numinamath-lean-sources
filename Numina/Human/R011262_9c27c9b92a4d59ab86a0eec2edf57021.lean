import Mathlib

open Polynomial

theorem algebra_236216 :
  {(p, q) : ℕ × ℕ | p.Prime ∧ q.Prime ∧ ∃ x y : ℤ, x ≠ y ∧ (X ^ 2 + C ↑p * X + C ↑q : ℤ[X]).roots = ↑[x, y]} = {(3, 2)} := by

  ext ⟨p, q⟩
  constructor
  · simp
    intro hp hq x₁ x₂ hne h_roots

    -- to use Vitae's theorem, we need to prove that x^2 + px + q splits in ℝ
    have h_eval_x₁ : (X ^ 2 + (p : ℤ[X]) * X + (q : ℤ[X]) : ℤ[X]).eval x₁ = 0 := by
      apply Polynomial.IsRoot.def.mp
      apply Polynomial.isRoot_of_mem_roots
      rw [h_roots]
      simp

    have h_eval_x₂ : (X ^ 2 + (p : ℤ[X]) * X + (q : ℤ[X]) : ℤ[X]).eval x₂ = 0 := by
      apply Polynomial.IsRoot.def.mp
      apply Polynomial.isRoot_of_mem_roots
      rw [h_roots]
      simp

    have h_poly_monic : Polynomial.Monic (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]) := by
      refine Monic.add_of_left ?_ ?_
      · refine monic_X_pow_add ?_
        simp
        have : (p : ℝ[X]).degree = 0 := by
          rw [show (p : ℝ[X]) = C ↑p by rfl]
          apply Polynomial.degree_C
          norm_cast
          exact Nat.Prime.ne_zero hp
        rw [this]
        norm_num
      · have : (q : ℝ[X]).degree = 0 := by
          rw [show (q : ℝ[X]) = C ↑q by rfl]
          apply Polynomial.degree_C
          norm_cast
          exact Nat.Prime.ne_zero hq
        rw [this]
        have : (X ^ 2 : ℝ[X]) + (p : ℝ[X]) * (X : ℝ[X]) = X * (X + (p : ℝ[X])) := by
          ring
        rw [this]
        rw [Polynomial.degree_mul]
        simp
        rw [show (X + (p : ℝ[X])) = X + (C p : ℝ[X]) by congr ,Polynomial.degree_X_add_C (p : ℝ)]
        norm_num

    have h_poly_deg_2 : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]).degree = 2 := by
      have : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]) = (X ^ 2 + (q : ℝ[X]) + (p : ℝ[X]) * X : ℝ[X]) := by ring
      rw [this]

      have : ((X ^ 2 : ℝ[X]) + (q : ℝ[X])).degree = 2 := by
        apply Polynomial.degree_X_pow_add_C
        norm_num
      rw [← this]

      refine degree_add_eq_left_of_degree_lt ?_
      rw [this]
      have : ((p : ℝ[X]) * (X : ℝ[X])).degree = 1 := by
        apply Polynomial.degree_C_mul_X
        norm_cast
        exact Nat.Prime.ne_zero hp
      rw [this]
      norm_num

    have h_poly_ne_zero : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]) ≠ 0 := by
      refine Monic.ne_zero ?_
      exact h_poly_monic

    have h_real_poly_roots: (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X])).roots = ↑[(x₁ : ℝ), (x₂ : ℝ)] := by
      refine Eq.symm (Multiset.eq_of_le_of_card_le ?_ ?_)
      · refine (Multiset.le_iff_subset ?_).mpr ?_
        · simp [hne]
        intro x xmem
        simp at xmem ⊢
        constructor
        · exact h_poly_ne_zero
        · rcases xmem with rfl | rfl
          · simp at h_eval_x₁
            norm_cast
          · simp at h_eval_x₂
            norm_cast
      · simp
        trans (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]).natDegree
        apply Polynomial.card_roots'
        have : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]).natDegree = (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]).degree := by
          exact Eq.symm (degree_eq_natDegree h_poly_ne_zero)
        suffices h : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]).degree ≤ 2 by
          rw [← this] at h
          norm_cast at h
        have : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X]) : ℝ[X]) =
          ((X ^ 2 : ℝ[X]) + (C q : ℝ[X])) + ((C p : ℝ[X]) * X : ℝ[X]) := by
          simp; ring
        rw [this]
        have : ((X ^ 2 : ℝ[X]) + (C q : ℝ[X])).degree ≤ 2 := by
          apply le_of_eq
          rw [Polynomial.degree_X_pow_add_C]
          norm_num
          norm_num
        have : ((C p : ℝ[X]) * X : ℝ[X]).degree ≤ 2 := by
          have : ((C p : ℝ[X]) * X : ℝ[X]).degree = 1 := by
            refine degree_C_mul_X ?_
            norm_cast
            exact Nat.Prime.ne_zero hp
          rw [this]
          norm_num
        apply Polynomial.degree_add_le_of_degree_le
        all_goals assumption

    have h_poly_splits : Splits (RingHom.id ℝ) (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X])) := by
      apply Polynomial.splits_iff_card_roots.mpr
      rw [h_real_poly_roots]
      simp
      symm
      refine (degree_eq_iff_natDegree_eq_of_pos (by norm_num)).mp ?_
      simp
      exact h_poly_deg_2

    -- Now Vitae's theorem says that x₁ + x₂ = -p
    have h_sum_roots := Polynomial.sum_roots_eq_nextCoeff_of_monic_of_split
      h_poly_monic h_poly_splits
    rw [h_real_poly_roots] at h_sum_roots

    have h_natdeg : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X])).natDegree = 2 := by
        exact (degree_eq_iff_natDegree_eq h_poly_ne_zero).mp h_poly_deg_2

    have : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X])).nextCoeff = ↑p := by
      have : (X ^ 2 + (p : ℝ[X]) * X + (q : ℝ[X])).natDegree > 0 := by
        rw [h_natdeg]
        norm_num
      rw [Polynomial.nextCoeff_of_natDegree_pos this]
      rw [h_natdeg, show 2 - 1 = 1 by norm_num]
      simp
    rw [this] at h_sum_roots
    simp at h_sum_roots
    norm_cast at h_sum_roots

    have h_x₁_add_x₂ : x₁ + x₂ = -p := by
      linarith only [h_sum_roots]

    -- and that x₁ * x₂ = q
    have h_prod_roots := Polynomial.prod_roots_eq_coeff_zero_of_monic_of_splits
      h_poly_monic h_poly_splits

    simp [h_natdeg, h_real_poly_roots] at h_prod_roots
    norm_cast at h_prod_roots

    -- Since q is a prime, either x₁ = ±1 or x₂ = ±1
    have : Irreducible (q : ℤ) := by
      refine Prime.irreducible ?_
      exact Nat.prime_iff_prime_int.mp hq
    have h_isunit := irreducible_iff.mp this |>.2 x₁ x₂ h_prod_roots

    clear h_eval_x₁ h_eval_x₂ h_poly_monic h_poly_deg_2 h_poly_ne_zero
    clear h_real_poly_roots h_natdeg h_sum_roots this h_poly_splits
    clear this

    -- wlog we can assimt x₁ = ±1, then x₂ = ±q
    wlog hx₁_unit : IsUnit x₁
    · have := this p q hp hq x₂ x₁ (fun eq ↦ hne eq.symm) ?_ (by linarith) ?_ h_isunit.symm
      simp [hx₁_unit] at h_isunit
      exact this h_isunit
      · rw [h_roots]; simp [hne];
        exact List.Perm.swap x₂ x₁ []
      · rw [h_prod_roots]; ring

    apply Int.isUnit_iff.mp at hx₁_unit
    rcases hx₁_unit with hx₁_pos | hx₁_neg
    · -- if x₁ = 1, then x₂ = q, so -p = x₁ + x₂ = q + 1, contradiction
      rw [hx₁_pos] at h_prod_roots
      simp at h_prod_roots
      have : x₁ + x₂ = q + 1 := by linarith
      have : -(p : ℤ) = q + 1 := by linarith
      have : q + 1 > (0 : ℤ) := by exact Int.succ_ofNat_pos q
      have : -(p : ℤ) ≤ 0 := by simp
      linarith
    · -- then x₁ = -1, and x₂ = -q
      rw [hx₁_neg] at h_prod_roots
      simp at h_prod_roots
      -- we have p = -(x₁ + x₂) = q + 1
      have : x₁ + x₂ = -q - 1 := by linarith
      have hp_eq : p = q + 1 := by linarith

      -- this can only happen when q = 2 and p = 3
      have : q ≤ 2 := by
        by_contra! h
        have : Odd q := by
          apply Nat.Prime.odd_of_ne_two hq
          exact Ne.symm (Nat.ne_of_lt h)
        have even_p : Even (q + 1) := by exact Odd.add_one this
        rw [← hp_eq] at even_p
        have odd_p : Odd p := by
          apply Nat.Prime.odd_of_ne_two hp
          linarith
        have : ¬ Even p := by exact Nat.not_even_iff_odd.mpr odd_p
        contradiction

      have : q ≥ 2 := by exact Nat.Prime.two_le hq
      repeat use (by linarith)
  · -- on the other hand, when q = 2, p = 3, the equation
    -- x^2 + 3x + 2 has integer solutions x₁ = -1 and x₂ = -2
    simp
    intro hp hq
    simp [hp, hq]
    norm_num
    use -1, -2
    norm_num
    have : (X : ℤ[X]) ^ 2 + 3 * X + 2 = (X + C 1) * (X + C 2) := by simp; ring
    rw [this]
    rw [Polynomial.roots_mul, Polynomial.roots_X_add_C, Polynomial.roots_X_add_C]
    rfl
    simp
    constructor
    · refine zero_le_degree_iff.mp ?_
      have : (1 : ℤ[X]) = C 1 := rfl
      rw [this, Polynomial.degree_X_add_C]
      norm_num
    · refine zero_le_degree_iff.mp ?_
      have : (2 : ℤ[X]) = C 2 := rfl
      rw [this, Polynomial.degree_X_add_C]
      norm_num
