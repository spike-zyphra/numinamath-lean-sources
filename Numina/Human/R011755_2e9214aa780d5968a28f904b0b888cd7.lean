import Mathlib

open Real Set
open scoped BigOperators

lemma quadratic_with_two_roots (a b c : ℝ) (ha : a ≠ 0) (h : discrim a b c > 0) :
    Set.encard {x : ℝ | a * x^2 + b * x + c = 0} = 2 := by
  obtain ⟨s, hs⟩ := show ∃ s : ℝ, discrim a b c = s^2 by
    use sqrt (discrim a b c)
    rw [Real.sq_sqrt]
    linarith
  suffices {x : ℝ | a * x^2 + b * x + c = 0} = {(-b + s) / (2 * a), (-b - s) / (2 * a)} by
    rw [this, Set.encard_eq_two]
    use (-b + s) / (2 * a), (-b - s) / (2 * a)
    split_ands
    · -- (-b + s) / (2 * a) ≠ (-b - s) / (2 * a)
      intro hs₁
      have ha₁ : 2 * a ≠ 0 := by
        intro ha₁
        apply ha
        linarith
      field_simp only [mul_eq_mul_right_iff, ha₁, or_false] at hs₁
      have hs₂ : s = 0 := by linarith
      rw [hs₂] at hs
      linarith
    · -- {(-b + s) / (2 * a), (-b - s) / (2 * a)} = {(-b + s) / (2 * a), (-b - s) / (2 * a)}
      simp
  rw [pow_two] at hs
  ext x
  have hx₂ := quadratic_eq_zero_iff ha hs x
  constructor <;> simp only [mem_setOf_eq, mem_insert_iff, mem_singleton_iff]
  · intro hx₁
    apply hx₂.mp
    linarith
  · intro hx₁
    rw [←hx₂] at hx₁
    linarith

theorem algebra_296312 : {a : ℝ | {x : ℝ | x ≠ 1 ∧ abs (x^2 / (x - 1)) = a}.encard = 2} = Set.Ioo 0 4 := by
  ext a
  constructor <;> simp only [mem_Ioo, ne_eq, mem_setOf_eq, and_imp]
  · intro hx
    -- because a = |x^2 / (x - 1)| and {x : ℝ | x ≠ 1 ∧ abs (x^2 / (x - 1)) = a} is not empty, so, 0 ≤ |x^2 / (x - 1)| = a
    have ha₁ : 0 ≤ a := by
      by_contra! ha₁
      absurd hx
      suffices {x | ¬x = 1 ∧ |x ^ 2 / (x - 1)| = a} = ∅ by
        rw [this]
        norm_num
      ext x; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hx₁ hx₂
      linarith [abs_nonneg (x^2 / (x - 1))]
    by_cases ha₂ : a = 0
    · -- if a = 0, then x^2 / (x - 1) = 0, so x = 0 or x = 1(in Lean4, x^2 / 0 = 0). But, we have x ≠ 1, so x = 0, which means that {x : ℝ | x ≠ 1 ∧ abs (x^2 / (x - 1)) = a} = {0}, and its encard = 1
      rw [ha₂] at hx
      norm_num at hx
      absurd hx
      suffices {x : ℝ | ¬x = 1 ∧ (x = 0 ∨ x - 1 = 0)} = {0} by
        rw [this]
        norm_num
      ext x
      constructor <;> simp only [mem_setOf_eq, mem_singleton_iff, and_imp]
      · rintro hx₁ (hx₂ | hx₃)
        · exact hx₂
        · absurd hx₁
          linarith
      · rintro rfl
        norm_num
    push_neg at ha₂
    use (lt_of_le_of_ne ha₁ ha₂.symm)
    -- Now, we need to prove that a < 4. At first, we need to convert |x ^ 2 / (x - 1)| = a to x^2 / (x - 1) = a or x^2 / (x - 1) = -a
    have hx₂ : {x : ℝ | ¬x = 1 ∧ |x ^ 2 / (x - 1)| = a} = {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))} := by
      ext x
      constructor <;> simp only [ne_eq, mem_setOf_eq, and_imp]
      · intro hx₁ hx₂
        use hx₁
        have hx₄ : x - 1 ≠ 0 := by
          intro hx₄
          apply hx₁
          linarith
        obtain (hx₃ | hx₃) := abs_choice (x ^ 2 / (x - 1))
        · rw [hx₃] at hx₂
          apply Or.inl
          field_simp only at hx₂
          linarith
        · rw [hx₃] at hx₂
          apply Or.inr
          field_simp only at hx₂
          linarith
      · intro hx₁ hx₂
        use hx₁
        have hx₄ : x - 1 ≠ 0 := by
          intro hx₄
          apply hx₁
          linarith
        obtain (hx₃ | hx₃) := hx₂
        · rw [show x^2 = a * (x - 1) by linarith]
          field_simp; linarith
        · rw [show x^2 = -a * (x - 1) by linarith, ←mul_div]
          field_simp; linarith
    rw [hx₂] at hx
    -- Then, we split {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))} to two parts: {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)} and {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)}
    have hx₃ : {x | x ≠ 1 ∧ (x ^ 2 - a * x + a = 0 ∨ x ^ 2 + a * x - a = 0)} = {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} ∪ {x : ℝ | x ≠ 1 ∧ x ^ 2 + a * x - a = 0} := by
      ext x; simp only [ne_eq, mem_setOf_eq, mem_union]
      tauto
    -- Because {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)} and {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)} are disjoint, so we can use encard_union_eq, which means that {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))}.encard = {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)}.encard + {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)}.encard
    have hx₄ : Disjoint {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} {x : ℝ | x ≠ 1 ∧ x ^ 2 + a * x - a = 0} := by
      rw [Set.disjoint_left]; simp only [ne_eq, mem_setOf_eq, not_and, and_imp]
      intro x hx₁ hx₂ hx₃ hx₄
      have hx₅ : (x - 1) * a = (x - 1) * (-a) := by linarith
      have hx₆ : x - 1 ≠ 0 := by
        intro hx₆
        apply hx₁
        linarith
      rw [mul_right_inj' hx₆] at hx₅
      apply ha₂
      linarith
    rw [hx₃, Set.encard_union_eq hx₄] at hx
    by_contra! ha₃
    have hx₅ : {x : ℝ | x ≠ 1 ∧ x^2 + a * x - a = 0}.encard = 2 := by
      suffices {x : ℝ | x ≠ 1 ∧ x^2 + a * x - a = 0} = {x : ℝ | 1 * x^2 + a * x - a = 0} by
        rw [this]
        apply quadratic_with_two_roots
        linarith
        rw [discrim]
        nlinarith
      ext x; simp only [ne_eq, mem_setOf_eq, one_mul, and_iff_right_iff_imp]
      intro hx₁ hx₂
      rw [hx₂] at hx₁
      norm_num at hx₁
    rw [hx₅] at hx
    absurd hx
    by_cases ha₄ : a = 4
    · -- if a = 4, then x^2 - 4 * x + 4 = 0 has one root
      rw [ha₄] at hx₅ ⊢
      suffices {x : ℝ | x ≠ 1 ∧ x^2 - 4 * x + 4 = 0} = {2}by
        rw [this]
        norm_num
      ext x
      constructor <;> simp only [ne_eq, mem_setOf_eq, mem_singleton_iff, and_imp]
      · intro hx₁ hx₂
        have hx₃ : (x - 2)^2 = 0 := by linarith
        simp only [sq_eq_zero_iff] at hx₃
        linarith
      · rintro rfl
        norm_num
    -- If a > 4, x^2 - a * x + a = 0 has two roots
    suffices {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0}.encard = 2 by
      rw [this]
      norm_num
    have hx₆ : {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} = {x : ℝ | 1 * x ^ 2 + (- a) * x + a = 0} := by
      ext x
      constructor <;> simp only [ne_eq, mem_setOf_eq, one_mul, neg_mul, and_imp]
      · intro hx₁ hx₂
        exact hx₂
      · intro hx₁
        refine ⟨?_, hx₁⟩
        intro hx₂
        rw [hx₂] at hx₁
        norm_num at hx₁
    rw [hx₆]
    apply quadratic_with_two_roots
    linarith
    rw [discrim]
    push_neg at ha₄
    nlinarith [lt_of_le_of_ne ha₃ ha₄.symm]
  · intro ha₁ ha₂
    have hx₂ : {x : ℝ | ¬x = 1 ∧ |x ^ 2 / (x - 1)| = a} = {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))} := by
      ext x
      constructor <;> simp only [mem_setOf_eq, ne_eq, and_imp]
      · intro hx₁ hx₂
        use hx₁
        have hx₄ : x - 1 ≠ 0 := by
          intro hx₄
          apply hx₁
          linarith
        obtain (hx₃ | hx₃) := abs_choice (x ^ 2 / (x - 1))
        · rw [hx₃] at hx₂
          apply Or.inl
          field_simp only at hx₂
          linarith
        · rw [hx₃] at hx₂
          apply Or.inr
          field_simp only at hx₂
          linarith
      · intro hx₁ hx₂
        use hx₁
        have hx₄ : x - 1 ≠ 0 := by
          intro hx₄
          apply hx₁
          linarith
        obtain (hx₃ | hx₃) := hx₂
        · rw [show x^2 = a * (x - 1) by linarith]
          field_simp; linarith
        · rw [show x^2 = -a * (x - 1) by linarith, ←mul_div]
          field_simp; linarith
    rw [hx₂]
    -- Then, we split {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))} to two parts: {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)} and {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)}
    have hx₃ : {x | x ≠ 1 ∧ (x ^ 2 - a * x + a = 0 ∨ x ^ 2 + a * x - a = 0)} = {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} ∪ {x : ℝ | x ≠ 1 ∧ x ^ 2 + a * x - a = 0} := by
      ext x; simp only [ne_eq, mem_setOf_eq, mem_union]
      tauto
    -- Because {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)} and {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)} are disjoint, so we can use encard_union_eq, which means that {x : ℝ | x ≠ 1 ∧ ((x^2 - a * x + a = 0) ∨ (x^2 + a * x - a = 0))}.encard = {x : ℝ | x ≠ 1 ∧ (x^2 - a * x + a = 0)}.encard + {x : ℝ | x ≠ 1 ∧ (x^2 + a * x - a = 0)}.encard
    have hx₄ : Disjoint {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} {x : ℝ | x ≠ 1 ∧ x ^ 2 + a * x - a = 0} := by
      rw [Set.disjoint_left]; simp only [ne_eq, mem_setOf_eq, not_and, and_imp]
      intro x hx₁ hx₂ hx₃ hx₄
      have hx₅ : (x - 1) * a = (x - 1) * (-a) := by linarith
      have hx₆ : x - 1 ≠ 0 := by
        intro hx₆
        apply hx₁
        linarith
      rw [mul_right_inj' hx₆] at hx₅
      linarith
    rw [hx₃, Set.encard_union_eq hx₄]
    have hx₅ : {x : ℝ | x ≠ 1 ∧ x^2 + a * x - a = 0}.encard = 2 := by
      suffices {x : ℝ | x ≠ 1 ∧ x^2 + a * x - a = 0} = {x : ℝ | 1 * x^2 + a * x - a = 0} by
        rw [this]
        apply quadratic_with_two_roots
        linarith
        rw [discrim]
        nlinarith
      ext x; simp only [ne_eq, mem_setOf_eq, one_mul, and_iff_right_iff_imp]
      intro hx₁ hx₂
      rw [hx₂] at hx₁
      norm_num at hx₁
    rw [hx₅]
    suffices {x : ℝ | x ≠ 1 ∧ x ^ 2 - a * x + a = 0} = ∅ by
      rw [this]
      norm_num
    ext x; simp only [ne_eq, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
    intro hx₁ hx₂
    rw [show x^2 = 1 * (x * x) by ring_nf, sub_eq_add_neg, show -(a * x) = (-a) * x by ring_nf, quadratic_eq_zero_iff_discrim_eq_sq (by simp)] at hx₂
    have : 0 ≤ discrim 1 (-a) a := by
      rw [hx₂]
      exact sq_nonneg (2 * 1 * x + -a)
    absurd this
    simp only [discrim]
    nlinarith
