import Mathlib

theorem Nat.div_eq_iff : ∀ {k x y : ℕ}, 0 < k → (x / k = y ↔ x ≤ y * k + k - 1 ∧ y * k ≤ x) := sorry

/-A number $n$ is called bummed out if there is exactly one ordered pair of positive integers $(x, y)$ such that

$$
\left\lfloor x^{2} / y\right\rfloor+\left\lfloor y^{2} / x\right\rfloor=n .
$$

Find all bummed out numbers.-/
theorem number_theory_611534 (bummed_out : ℕ → Prop)
    (h : ∀ n, bummed_out n ↔ {(x, y) : ℕ × ℕ|0 < x ∧ 0 < y ∧ x ^ 2 / y + y ^ 2 / x = n}.ncard = 1) :
    ∀ n, bummed_out n ↔ n = 2 ∨ n = 6 ∨ n = 8 ∨ n = 10 := by
-- Unfold the definition of `bummed out` and rewrite the ncard assumption
  intro n; rw [h, Set.ncard_eq_one]
  simp [Set.ext_iff]; constructor
  -- Assume we have such a pair $(x, y)$, prove that $x=y$
  · rintro ⟨x, y, h'⟩; have hxy := h' x y
    simp at hxy; rcases hxy with ⟨xpos, ypos, hxy⟩
    have := (h' y x).mp (by exact ⟨ypos, xpos, by rw [← hxy]; ring⟩)
    rcases this with ⟨yeqx⟩; replace hxy : n = 2 * x := by
      rw [yeqx, pow_two, Nat.mul_div_cancel] at hxy
      rw [← hxy]; ring; omega
  -- Prove that $x$ must be less than $6$ since otherwise $(x+1,x-1)$ will be another pair satisfying the assumption
    by_cases h'' : 6 ≤ x
    · have h1 : (x - 1) ^ 2 / (x + 1) = x - 3 := by
        rw [Nat.div_eq_iff]; constructor
        · zify; repeat rw [Nat.cast_sub]
          push_cast; rw [Nat.cast_sub]; push_cast
          rw [← sub_nonneg]; ring_nf; all_goals omega
        zify; repeat rw [Nat.cast_sub]
        push_cast; rw [← sub_nonneg]
        ring_nf; all_goals omega
      have h2 : (x + 1) ^ 2 / (x - 1) = x + 3 := by
        rw [Nat.div_eq_iff]; constructor
        · zify; repeat rw [Nat.cast_sub]
          push_cast; rw [Nat.cast_sub]; push_cast
          rw [← sub_nonneg]; ring_nf; all_goals omega
        zify; repeat rw [Nat.cast_sub]
        push_cast; rw [← sub_nonneg]
        ring_nf; all_goals omega
      have := (h' (x+1) (x-1)).mp (by exact ⟨by omega, by omega, by rw [h1, h2, hxy]; omega⟩)
      omega
  -- Check all possible values of $x$ and exclude $x=2$
    push_neg at h''; interval_cases x; any_goals simp [hxy]
    simp [hxy, yeqx] at h'
    have := (h' 2 1).mp (by simp); omega
-- Conversely, it is straightforward to check that the given values of $n$ are all bummed out
  intro hn; clear bummed_out h; rcases hn with hn|hn|hn|hn
  -- When $n=2$, fulfill the goal with $(1, 1)$
  · rw [hn]; clear hn; use 1, 1; intro x y; constructor
    · rintro ⟨xpos, ypos, hxy⟩; wlog xley : x ≤ y
      · specialize this 2 y x ypos xpos (by nth_rw 3 [← hxy]; ring)
        rw [and_comm]; exact this (by omega)
      have : y ≤ y ^ 2 / x := by
        rw [Nat.le_div_iff_mul_le, pow_two]
        gcongr; omega
    -- Prove that $y$ is less than $2$, then check all possible values of $y$
      replace this : y ≤ 2 := by
        rw [← hxy]; exact le_add_left this
      interval_cases y; any_goals interval_cases x
      any_goals simp at hxy
      simp
    rintro ⟨hx, hy⟩; simp [hx, hy]
  -- When $n=6$, fulfill the goal with $(3, 3)$
  · rw [hn]; clear hn; use 3, 3; intro x y; constructor
    · rintro ⟨xpos, ypos, hxy⟩; wlog xley : x ≤ y
      · specialize this 2 y x ypos xpos (by rw [← hxy]; ring)
        rw [and_comm]; exact this (by omega)
      have : y ≤ y ^ 2 / x := by
        rw [Nat.le_div_iff_mul_le, pow_two]
        gcongr; omega
    -- Prove that $y$ is less than $6$, then check all possible values of $y$
      replace this : y ≤ 6 := by
        rw [← hxy]; exact le_add_left this
      interval_cases y; any_goals interval_cases x
      any_goals simp at hxy
      simp
    rintro ⟨hx, hy⟩; simp [hx, hy]
  -- When $n=8$, fulfill the goal with $(4, 4)$
  · rw [hn]; clear hn; use 4, 4; intro x y; constructor
    · rintro ⟨xpos, ypos, hxy⟩; wlog xley : x ≤ y
      · specialize this 2 y x ypos xpos (by rw [← hxy]; ring)
        rw [and_comm]; exact this (by omega)
      have : y ≤ y ^ 2 / x := by
        rw [Nat.le_div_iff_mul_le, pow_two]
        gcongr; omega
    -- Prove that $y$ is less than $8$, then check all possible values of $y$
      replace this : y ≤ 8 := by
        rw [← hxy]; exact le_add_left this
      interval_cases y; any_goals interval_cases x
      any_goals simp at hxy
      simp
    rintro ⟨hx, hy⟩; simp [hx, hy]
  -- When $n=10$, fulfill the goal with $(5, 5)$
  · rw [hn]; clear hn; use 5, 5; intro x y; constructor
    · rintro ⟨xpos, ypos, hxy⟩; wlog xley : x ≤ y
      · specialize this 2 y x ypos xpos (by rw [← hxy]; ring)
        rw [and_comm]; exact this (by omega)
      have : y ≤ y ^ 2 / x := by
        rw [Nat.le_div_iff_mul_le, pow_two]
        gcongr; omega
    -- Prove that $y$ is less than $10$, then check all possible values of $y$
      replace this : y ≤ 10 := by
        rw [← hxy]; exact le_add_left this
      interval_cases y; any_goals interval_cases x
      any_goals simp at hxy
      simp
    rintro ⟨hx, hy⟩; simp [hx, hy]