import Mathlib

open Real Set
open scoped BigOperators

/- 7. If the equation $\cot (\arcsin x)=\sqrt{a^{2}-x^{2}}$ has real solutions for $x$, then the range of real values for $a$ is $\qquad$ . -/

-- lemma realting cot(arcsin (x))
lemma l_cot_arcsin {x : ℝ} : cot (arcsin x) = √(1 - x^2) / x := by
  rw [cot_eq_cos_div_sin, cos_arcsin]
  by_cases hx₁ : -1 ≤ x; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  by_cases hx₂ : x ≤ 1; swap
  · have h : √(1 - x ^ 2) = 0 := sqrt_eq_zero_of_nonpos (by nlinarith)
    rw [h]
    simp
  rw [sin_arcsin hx₁ hx₂]

-- if set is empty then it has an element
lemma l_nonempty {s : Set ℝ} (h : s ≠ ∅) : ∃ x, x ∈ s := by
  simp [EmptyCollection.emptyCollection] at h
  contrapose h
  push_neg at h ⊢
  ext x
  simp [Membership.mem, Set.Mem]
  specialize h x
  assumption

theorem algebra_101727 (a : ℝ) :
    {x : ℝ | arcsin x ≠ 0 ∧ 0 ≤ a^2 - x^2 ∧ -1 ≤ x ∧ x ≤ 1 ∧ cot (arcsin x) = sqrt (a^2 - x^2)} ≠ ∅ ↔
    a ≤ -1 ∨ a ≥ 1 := by
  -- convert the set to easier version, changing trigonometry and bound of [-1, 1]
  have : {x : ℝ | arcsin x ≠ 0 ∧ 0 ≤ a^2 - x^2 ∧ -1 ≤ x ∧ x ≤ 1 ∧ cot (arcsin x) = sqrt (a^2 - x^2)} =
      {x : ℝ | x ≠ 0 ∧ 0 ≤ a^2 - x^2 ∧ x^2 ≤ 1 ∧ √(1 - x^2) / x = √ (a^2 - x^2)} := by
    ext x;
    simp
    rw [l_cot_arcsin]
    rintro hx1 hx2
    rw [← and_assoc]
    simp
    rintro hx3
    rw [abs_le]
  rw [this]
  constructor
  -- proving nonempty set to a's range
  . rintro h
    replace h := l_nonempty h
    obtain ⟨x, hx1, hx2, hx3, hx4⟩ := h
    simp at hx1
    -- convert the equation to quadratic equaiton of x^2
    field_simp at hx4
    have hx3' : 0 ≤ 1 - x^2 := by linarith
    replace hx4 := congrArg (fun x ↦ x^2) hx4
    simp [mul_pow, hx3', hx2] at hx4
    replace hx4 : 1 * (x^2 * x^2) + (-(a^2 + 1)) * x^2 + 1 = 0 := by linarith
    -- quadratic equaiton has solution, so discriminant is a square hence positive
    rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)] at hx4
    replace hx4 : 0 ≤ discrim 1 (-(a ^ 2 + 1)) 1 := by rw [hx4]; positivity
    simp [discrim] at hx4
    replace hx4 : 2^2 ≤ (a^2 + 1)^2 := by linarith
    rw [sq_le_sq₀ (by norm_num) (by positivity)] at hx4
    -- convert 1 ≤ a^2 to goal
    replace hx4 : 1^2 ≤ a^2 := by linarith
    by_cases ha : 0 ≤ a
    . rw [sq_le_sq₀ (by norm_num) ha] at hx4
      simp [hx4]
    . simp at ha
      rw [← neg_sq (a := a)] at hx4
      rw [sq_le_sq₀ (by norm_num) (by linarith)] at hx4
      left
      linarith
  -- proving a's bounds to nonempty set
  . rintro h
    -- convert a's bound to 1 ≤ a^2
    replace h : 1 ≤ a^2 := by
      obtain h | h := h
      . replace h : 1 ≤ -a := by linarith
        rw [← sq_le_sq₀ (by norm_num) (by linarith)] at h
        linarith
      . replace h : 1 ≤ a := by linarith
        rw [← sq_le_sq₀ (by norm_num) (by linarith)] at h
        linarith
    -- proving one solution is enough
    suffices ∃ x, x ∈ {x | x ≠ 0 ∧ 0 ≤ a ^ 2 - x ^ 2 ∧ x ^ 2 ≤ 1 ∧ √(1 - x ^ 2) / x = √(a ^ 2 - x ^ 2)} by
      by_contra h'
      obtain ⟨x, hx⟩ := this
      rw [h'] at hx
      simp at hx
    -- following 3 reuslts are used later,
    have : 0 ≤ -3 + a ^ 2 * 2 + a ^ 4 := by
      suffices 2 ^ 2 ≤ (a^2 + 1)^2 by linarith
      rw [sq_le_sq₀ (by norm_num) (by positivity)]
      linarith
    have ha1 : √((a^2 + 1)^2 - 4) < a^2 + 1 := by
      calc
        _ < √((a^2 + 1)^2) := by
          apply sqrt_lt_sqrt
          . ring_nf
            linarith
          . linarith
        _ = _ := by
          rw [sqrt_sq]
          positivity
    have ha2 : a^2 - 1 ≤ √((a^2 + 1)^2 - 4) := by
      rw [← sq_le_sq₀ (by linarith) (by ring_nf; positivity)]
      rw [sq_sqrt (by ring_nf; positivity)]
      linarith
    -- we will use following x as solution
    set x := √((a ^ 2 + 1 - √((a ^ 2 + 1) ^ 2 - 4)) / 2) with hx
    have hx2 : x^2 ≤ 1 := by
      rw [hx, sq_sqrt (by linarith)]
      linarith
    use x
    simp only [ne_eq, sub_nonneg, Nat.ofNat_nonneg, sqrt_div',
      mem_setOf_eq, div_eq_zero_iff, sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false]
    -- the inequalities are easy to prove
    and_intros
    . rw [Real.sqrt_eq_zero']
      simp
      linarith
    . linarith
    . linarith
    -- to prove it satisfies equation, prove 0 < x then convert it to quadratic equation of x^2 and show discriminant is required square
    . have : 0 < x := by
        rw [hx]
        have : 0 < a ^ 2 + 1 - √((a ^ 2 + 1) ^ 2 - 4) := by linarith
        positivity
      field_simp
      rw [← sq_eq_sq₀ (by positivity) (by positivity)]
      rw [sq_sqrt (by linarith), mul_pow]
      have : √(a ^ 2 - x ^ 2) ^ 2 = a ^ 2 - x ^ 2 := by
        rw [sq_sqrt]
        linarith
      rw [this]
      suffices 1 * (x^2 * x^2) + (-(a^2 + 1)) * x^2 + 1 = 0 by linarith
      rw [quadratic_eq_zero_iff_discrim_eq_sq (by norm_num)]
      rw [hx, sq_sqrt (by linarith)]
      ring_nf
      rw [sq_sqrt (by linarith)]
      simp [discrim]
      ring