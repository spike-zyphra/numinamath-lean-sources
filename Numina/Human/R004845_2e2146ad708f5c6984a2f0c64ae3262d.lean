import Mathlib

open Polynomial Complex Real

/- We prove a lemma about ℤ[X] polynomials evaluated at $a+b\sqrt{5}$ and $a-b\sqrt{5}$, where $a,b$ are integers.
  The results are 'conjugates' of each other, and we can express the result as $m+-n\sqrt{5}$, where $m,n$ are integers.-/
lemma int_polynomial_eval₂_conjugate (P : Polynomial ℤ) (a b : ℤ) (c : ℕ) :
    ∃ m n : ℤ, P.eval₂ (Int.castRingHom ℝ) (a + b * √c) = m + n * √c ∧ P.eval₂ (Int.castRingHom ℝ) (a - b * √c) = m - n * √c := by
  induction P using Polynomial.induction_on
  · rename_i e
    use e, 0
    rw [eval₂_C, eval₂_C]
    simp
  · rename_i p q ih₁ ih₂
    obtain ⟨m₁, n₁, h₁, h₂⟩ := ih₁
    obtain ⟨m₂, n₂, h₃, h₄⟩ := ih₂
    use m₁ + m₂, n₁ + n₂
    rw [eval₂_add, eval₂_add]
    simp [h₁, h₂, h₃, h₄]
    constructor <;> ring
  · rename_i d e ih
    rw [eval₂_mul, eval₂_mul, eval₂_C, eval₂_C, eval₂_X_pow, eval₂_X_pow] at ih ⊢
    obtain ⟨m, n, h₁, h₂⟩ := ih
    rw [pow_add, pow_add, pow_one, pow_one, ←mul_assoc, ←mul_assoc, h₁, h₂]
    use m * a + n * b * c, m * b + n * a
    constructor <;>
    all_goals
      ring_nf
      rw [sq_sqrt]
      · simp
        ring
      · simp

/-Does it exist? a polynomial $P(x)$ with integer coefficients, such that $P(1+\sqrt{3})=2+\sqrt{3}$ and $P(3+\sqrt{5})=3+\sqrt{5}$.-/
theorem inequalities_604202 : ¬ ∃ P : Polynomial ℤ, P.eval₂ (Int.castRingHom ℝ) (1 + √3) = 2 + √3 ∧
    P.eval₂ (Int.castRingHom ℝ) (3 + √5) = 3 + √5 := by
  -- The answer is No.
  intro h
  obtain ⟨P, hP₁, hP₂⟩ := h
  let R : ℝ[X] := P.map (Int.castRingHom ℝ) - X
  -- have hR_eval_complex {x : ℂ} : R.eval x = P.eval₂ (Int.castRingHom ℂ) x - x := by
  --   simp [R]
  --   exact eval_map (Int.castRingHom ℂ) x
  have hR_eval_real {x : ℝ} : R.eval x = P.eval₂ (Int.castRingHom ℝ) x - x := by
    simp [R]
    exact eval_map (Int.castRingHom ℝ) x
    -- rw [←ofRealHom_eq_coe, ←ofRealHom_eq_coe]
    -- rw [ringHom_eval₂_intCastRingHom]

  -- The polynomial $P(x)-x$ has root $3+\sqrt{5}$,
  have hR₁ : R.IsRoot (3 + √5) := by
    simp
    -- rw [show (3 + √5 : ℂ) = (3 + √5 : ℝ) by simp]
    rw [hR_eval_real, hP₂, sub_self]

  -- and since it has integer coefficients, it also has root $3-\sqrt{5}$.
  have hR₂ : R.IsRoot (3 - √5) := by
    obtain ⟨m, n, h₁, h₂⟩ := int_polynomial_eval₂_conjugate (P - X) 3 1 5
    simp at h₁ h₂
    simp [R, eval_map, h₁] at hR₁
    have hn : n = 0 := by
      have : -m = n * √5 := by linarith only [hR₁]
      by_contra h
      have hr : Irrational (n * √5) := by
        simp [h]
        refine irrational_sqrt_ofNat_iff.mpr ?_
        refine Prime.not_square ?_
        refine Nat.prime_iff.mp ?_
        norm_num
      simp [←this] at hr
    have hm : m = 0 := by
      simp [hn] at hR₁
      exact hR₁
    simp [R, eval_map, h₂, hm, hn]


  -- The quadratic having these two roots is $x^{2}-6 x+4$.
  apply dvd_iff_isRoot.mpr at hR₁
  apply dvd_iff_isRoot.mpr at hR₂
  have hR₃ : (X - C (3 + √5)) * (X - C (3 - √5)) ∣ R := by
    apply IsCoprime.mul_dvd ?_ hR₁ hR₂
    apply Polynomial.isCoprime_X_sub_C_of_isUnit_sub
    simp
  have hR₄ : (X - C (3 + √5)) * (X - C (3 - √5)) = X ^ 2 - 6 * X + 4 := by
    apply Polynomial.funext
    intro r
    simp
    ring_nf
    rw [sq_sqrt]
    · norm_cast
      ring
    · simp
  rw [hR₄] at hR₃
  have hR₅ : (X ^ 2 - 6 * X + 4) ∣ P - X := by
    refine (map_dvd_map (Int.castRingHom ℝ) ?_ ?_).mp ?_
    · exact RingHom.injective_int (Int.castRingHom ℝ)
    · refine Monic.def.mpr ?_
      unfold Polynomial.leadingCoeff
      have : (X ^ 2 - 6 * X + 4 : ℤ[X]).natDegree = 2 := by
        rw [natDegree_add_eq_left_of_natDegree_lt]
        rw [natDegree_sub_eq_left_of_natDegree_lt]
        · simp
        · simp
        · rw [natDegree_sub_eq_left_of_natDegree_lt]
          · simp
          · simp
      simp [this]
      rw [coeff_X]
      simp
    · simp
      exact hR₃

  -- Therefore $P(x)-x=\left(x^{2}-6 x+4\right) Q(x)$ for some polynomial $Q(x)$ with integer coefficients.
  obtain ⟨Q, hQ⟩ := hR₅
  have hQ : P = (X ^ 2 - 6 * X + 4) * Q + X := by
    rw [←hQ]
    ring_nf
  simp [hQ] at hP₁
  apply eq_sub_of_add_eq at hP₁
  -- Plugging in $x=1+\sqrt{3}$ we find $1=(2-4 \sqrt{3}) Q(1+\sqrt{3})$.
  have hQ₁ : 1 = (2 - 4 * √3) * Q.eval₂ (Int.castRingHom ℝ) (1 + √3) := by
    symm
    apply Eq.trans ?_ (Eq.trans hP₁ ?_)
    · congr
      apply sub_eq_zero.mp
      ring_nf
      rw [sq_sqrt]
      all_goals simp
    · ring

  -- From known conjugates properties we also do have $1=(2+4 \sqrt{3}) Q(1-\sqrt{3})$,
  have hQ₂ : 1 = (2 + 4 * √3) * Q.eval₂ (Int.castRingHom ℝ) (1 - √3) := by
    let P : ℤ[X] := (6 - 4 * X) * Q
    obtain ⟨m, n, h₁, h₂⟩ := int_polynomial_eval₂_conjugate P 1 1 3
    simp [P] at h₁ h₂
    have : 6 - 4 * (1 + √3) = 2 - 4 * √3 := by ring_nf
    rw [this, ←hQ₁] at h₁
    have : 6 - 4 * (1 - √3) = 2 + 4 * √3 := by ring_nf
    rw [this] at h₂
    have hn : n = 0 := by
      have : 1 - m = n * √3 := by linarith only [h₁]
      by_contra h
      have hr : Irrational (n * √3) := by
        simp [h]
        refine irrational_sqrt_ofNat_iff.mpr ?_
        refine Prime.not_square ?_
        refine Nat.prime_iff.mp ?_
        norm_num
      simp [←this] at hr
    have hm : m = 1 := by
      simp [hn] at h₁
      norm_cast at h₁
      rw [h₁]
    simp [hm, hn] at h₂
    nth_rw 1 [←h₂]

  -- so (multiply) $1=-44 Q(1+\sqrt{3}) Q(1-\sqrt{3})$, impossible, since again by the properties of conjugates
  have hQ₃ : 1 = -44 * (Q.eval₂ (Int.castRingHom ℝ) (1 + √3) * Q.eval₂ (Int.castRingHom ℝ) (1 - √3)) := by
    nth_rw 1 [show (1 : ℝ) = 1 * 1 by simp]
    nth_rw 1 [hQ₁]
    nth_rw 2 [hQ₂]
    have : -44 = (2 - 4 * √3) * (2 + 4 * √3) := by
      ring_nf
      rw [sq_sqrt]
      · ring
      · simp
    rw [this]
    ring

  -- $$ Q(1+\sqrt{3}) Q(1-\sqrt{3})=Q(1+\sqrt{3}) Q(\overline{1+\sqrt{3}})=Q(1+\sqrt{3}) \overline{Q(1+\sqrt{3})} $$
  -- must be some integer $k$, and we cannot have $1=-44 k$.
  have ⟨k, hk⟩ : ∃ k : ℤ, k = Q.eval₂ (Int.castRingHom ℝ) (1 + √3) * Q.eval₂ (Int.castRingHom ℝ) (1 - √3) := by
    obtain ⟨m, n, h₁, h₂⟩ := int_polynomial_eval₂_conjugate Q 1 1 3
    simp at h₁ h₂
    rw [h₁, h₂]
    ring_nf
    rw [sq_sqrt]
    · use m ^ 2 - n ^ 2 * 3
      norm_cast
    · simp
  rw [←hk] at hQ₃
  norm_cast at hQ₃
  have : -44 ∣ 1 := by use k; rw [hQ₃]; simp
  norm_num at this
