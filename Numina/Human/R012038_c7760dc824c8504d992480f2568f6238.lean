import Mathlib

theorem inequalities_319894 : {m : ℝ | {x : ℤ | abs (x - 1) < x + 2 ∧ x < m}.encard = 2} = Set.Ioc 1 2 := by
  ext m
  constructor <;> simp
  · -- {x | |x - 1| < x + 2 ∧ ↑x < m}.encard = 2 → 1 < m ∧ m ≤ 2
    intro h₁
    -- We show that ↑x < m means x < ⌈m⌉ firstly.
    have : {x : ℤ | |x - 1| < x + 2 ∧ ↑x < m} = {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} := by
      ext x
      constructor <;> simp
      · intro hx₁ hx₂
        use hx₁
        exact Int.lt_ceil.mpr hx₂
      · intro hx₁ hx₂
        use hx₁
        exact Int.lt_ceil.mp hx₂
    rw [this] at h₁
    -- If m ≤ 0, then {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = ∅
    by_cases hm₁ : m ≤ 0
    · suffices {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = ∅ by
        rw [this] at h₁
        norm_num at h₁
      -- We need to show that {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = ∅ now.
      ext x; simp
      intro hx₁
      have hx₂ : 0 ≤ x := by
        obtain (hx | hx) := abs_choice (x - 1)
        · have := abs_nonneg (x - 1)
          rw [hx] at this
          linarith
        · rw [hx] at hx₁
          linarith
      apply le_trans ?_ hx₂
      apply Int.ceil_le.mpr
      norm_num
      assumption
    push_neg at hm₁
    -- If 0 < m ≤ 1, then {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = {0}
    by_cases hm₂ : m ≤ 1
    · suffices {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = {0} by
        rw [this] at h₁
        norm_num at h₁
      -- We need to show that {x : ℤ | |x - 1| < x + 2 ∧ x < ⌈m⌉} = {0} now.
      ext x
      constructor <;> simp
      · intro hx₁ hx₂
        have : ⌈m⌉ = 1 := by
          apply Int.ceil_eq_on_Ioc 1 m
          simp
          exact ⟨hm₁, hm₂⟩
        rw [this] at hx₂
        rw [abs_eq_neg_self.mpr (by linarith)] at hx₁
        linarith
      · intro hx₁
        rw [hx₁]
        norm_num
        linarith
    push_neg at hm₂
    use hm₂
    -- If 2 < m, the number of integers x satisfying |x - 1| < x + 2 ∧ x < ⌈m⌉ is at least 3
    by_contra! hm₃
    suffices Set.encard {x | |x - 1| < x + 2 ∧ x < ⌈m⌉} ≥ 3 by
      rw [h₁] at this
      norm_num at this
    suffices {0, 1, 2} ⊆ {x | |x - 1| < x + 2 ∧ x < ⌈m⌉} by
      norm_num
      apply le_trans (le_of_eq ?_) (Set.encard_le_card this)
      rw [Eq.comm, Set.encard_eq_three]
      use 0, 1, 2
      simp
    rw [Set.subset_def]; simp
    rw [Int.lt_ceil, Int.lt_ceil]
    norm_cast
  · -- 1 < m → m ≤ 2 → {x | |x - 1| < x + 2 ∧ ↑x < m}.encard = 2
    intro hm₁ hm₂
    -- If {x : ℤ | |x - 1| < x + 2 ∧ x < m} = {0, 1}, then {x : ℤ | |x - 1| < x + 2 ∧ x < m}.encard = 2
    suffices {x : ℤ | |x - 1| < x + 2 ∧ x < m} = {0, 1} by
      rw [this, Set.encard_eq_two]
      use 0, 1
      simp
    -- Now, we need to show that {x : ℤ | |x - 1| < x + 2 ∧ x < m} = {0, 1}
    ext x
    constructor <;> simp
    · -- |x - 1| < x + 2 → ↑x < m → x = 0 ∨ x = 1
      intro hx₁ hx₂
      -- From x < m, and 1 < m ≤ 2, we have x ≤ 1
      have hx₃ : x ≤ 1 := by
        apply Int.le_of_lt_add_one
        apply lt_of_lt_of_le (Int.lt_ceil.mpr hx₂)
        exact Int.ceil_le.mpr hm₂
      rw [abs_eq_neg_self.mpr (by linarith)] at hx₁
      omega
    · -- x = 0 ∨ x = 1 → |x - 1| < x + 2 ∧ ↑x < m
      rintro (hx | hx) <;> {
        rw [hx]
        norm_num
        linarith
      }
