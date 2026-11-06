import Mathlib

open Real Set
open scoped BigOperators

lemma quadratic_has_two_roots_of_discrim_pos {a b c : ℝ} (ha : a ≠ 0) (h : discrim a b c > 0) :
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
      field_simp [ha₁] at hs₁
      have hs₂ : s = 0 := by linarith
      rw [hs₂] at hs
      linarith
    · -- {(-b + s) / (2 * a), (-b - s) / (2 * a)} = {(-b + s) / (2 * a), (-b - s) / (2 * a)}
      simp
  rw [pow_two] at hs
  ext x
  have hx₂ := quadratic_eq_zero_iff ha hs x
  constructor <;> simp
  · intro hx₁
    apply hx₂.mp
    linarith
  · intro hx₁
    rw [←hx₂] at hx₁
    linarith

theorem algebra_622056 : {a : ℝ | {x : ℝ | x^4 - 2 * a * x^2 - x + a^2 - a = 0}.encard = 2} = Set.Ioc (-1/4) (3/4) := by
  ext a
  have h₁ : {x : ℝ | x^4 - 2 * a * x^2 - x + a^2 - a = 0} = {x : ℝ | x^2 + x + 1 - a = 0} ∪ {x : ℝ | x^2 - x - a = 0} := by
    ext x
    constructor <;> simp
    · intro hx₁
      have : (x^2 + x + 1 - a) * (x^2 - x - a) = 0 := by
        ring_nf
        linarith
      simp at this
      exact this
    · intro hx₁
      rw [show x^4 - 2 * a * x^2 - x + a^2 - a = (x^2 + x + 1 - a) * (x^2 - x - a) by ring_nf]
      simp
      exact hx₁
  constructor <;> simp
  · rw [h₁]
    intro ha₁
    by_cases ha₂ : a ≤ -1/4
    · have h₃ : {x | x ^ 2 + x + 1 - a = 0} = ∅ := by
        ext x; simp
        intro hx₁
        rw [show x ^ 2 + x + 1 - a = 1 * (x * x) + 1 * x + (1 - a) by ring_nf, quadratic_eq_zero_iff_discrim_eq_sq (by simp)] at hx₁
        have : 0 ≤ discrim 1 1 (1 - a) := by
          rw [hx₁]
          apply sq_nonneg
        absurd this
        simp [discrim]
        linarith
      rw [h₃] at ha₁
      simp at ha₁
      by_cases ha₃ : a = -1/4
      · have : {x | x ^ 2 - x - a = 0} = {1/2} := by
          ext x
          constructor <;> simp
          · intro hx₁
            have hx₂ : (x - (1/2)) * (x - (1/2)) = 0 := by
              ring_nf
              linarith
            simp at hx₂
            linarith
          · intro hx₁
            rw [hx₁, ha₃]
            norm_num
        rw [this] at ha₁
        simp at ha₁
      suffices {x | x ^ 2 - x - a = 0} = ∅ by
        rw [this] at ha₁
        simp at ha₁
      ext x; simp
      intro hx₁
      rw [show x ^ 2 - x - a = 1 * (x * x) + (-1) * x + (- a) by ring_nf, quadratic_eq_zero_iff_discrim_eq_sq (by simp)] at hx₁
      have : 0 ≤ discrim 1 (-1) (-a) := by
        rw [hx₁]
        apply sq_nonneg
      absurd this
      simp [discrim]
      linarith [lt_of_le_of_ne ha₂ ha₃]
    push_neg at ha₂
    use ha₂
    by_contra! ha₃
    have h₂ : Disjoint {x | x ^ 2 + x + 1 - a = 0} {x | x ^ 2 - x - a = 0} := by
      rw [Set.disjoint_left]; simp
      intro x hx₁ hx₂
      have hx₃ : x = -1/2 := by nlinarith
      rw [hx₃] at hx₁ hx₂
      norm_num at hx₁ hx₂
      linarith
    rw [Set.encard_union_eq h₂] at ha₁
    suffices {x | x ^ 2 + x + 1 - a = 0}.encard = 2 ∧ {x | x ^ 2 - x - a = 0}.encard = 2 by
      rw [this.1, this.2] at ha₁
      norm_num at ha₁
    split_ands
    · have : {x | x ^ 2 + x + 1 - a = 0} = {x | 1 * x ^ 2 + 1 * x + (1 - a) = 0} := by
        ext x; simp
        ring_nf
      rw [this]
      apply quadratic_has_two_roots_of_discrim_pos (by simp)
      rw [discrim]
      ring_nf
      linarith
    · have : {x | x ^ 2 - x - a = 0} = {x | 1 * x ^ 2 + (-1) * x - a = 0} := by
        ext x; simp
        ring_nf
      rw [this]
      apply quadratic_has_two_roots_of_discrim_pos (by simp)
      rw [discrim]
      linarith
  · intro ha₁ ha₂
    by_cases ha₃ : a = 3/4
    · have h₂ : {x | x ^ 4 - 2 * a * x ^ 2 - x + a ^ 2 - a = 0} = {-1/2, 3/2} := by
        ext x; rw [ha₃]
        constructor <;> simp
        · intro hx₁
          have hx₂ : (x + 1/2)^3 * (x - 3/2) = 0 := by
            ring_nf
            linarith
          simp at hx₂
          obtain (hx₂ | hx₂) := hx₂
          · apply Or.inl
            linarith
          · apply Or.inr
            linarith
        · rintro (rfl | rfl)
          all_goals norm_num
      rw [h₂, Set.encard_eq_two]
      use (-1/2), 3/2
      norm_num
    rw [h₁]
    have h₂ : {x | x ^ 2 - x - a = 0}.encard = 2 := by
      have : {x | x ^ 2 - x - a = 0} = {x | 1 * x ^ 2 + (-1) * x - a = 0} := by
        ext x; simp
        ring_nf
      rw [this]
      apply quadratic_has_two_roots_of_discrim_pos (by simp)
      rw [discrim]
      linarith
    have h₃ : {x | x ^ 2 + x + 1 - a = 0} = ∅ := by
      ext x; simp
      intro hx₁
      rw [show x ^ 2 + x + 1 - a = 1 * (x * x) + 1 * x + (1 - a) by ring_nf, quadratic_eq_zero_iff_discrim_eq_sq (by simp)] at hx₁
      have : 0 ≤ discrim 1 1 (1 - a) := by
        rw [hx₁]
        apply sq_nonneg
      absurd this
      simp [discrim]
      linarith [lt_of_le_of_ne ha₂ ha₃]
    rw [h₃]
    simp
    exact h₂
