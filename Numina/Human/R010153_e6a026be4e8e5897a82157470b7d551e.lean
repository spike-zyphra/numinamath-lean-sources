import Mathlib

/- What is the sum of the positive integers $k$ such that $\frac{k}{27}$ is greater than $\frac{2}{3}$ and less than $\frac{8}{9}$? -/
theorem algebra_20266{s: Finset ℕ}
  (hs: s = {x : ℕ | (2/3:ℚ)<x/27 ∧ x/27<(8/9:ℚ) } ):
  ∑ k ∈ s, k = 105 := by
  -- 2/3 = 18/27 and 8/9 = 24/27, so k is between 18 and 24
  have h1: {x : ℕ | (2/3:ℚ)<x/27 ∧ x/27<(8/9:ℚ) } =
    {x:ℕ | 18 < x ∧ x < 24} := by
    ext x; simp
    have hh1: (2/3:ℚ) = 18/27 := by norm_num
    have hh2: (8/9:ℚ) = 24/27 := by norm_num
    rw [hh1, hh2]
    constructor <;> intro h
    <;> have lb := h.left
    <;> have ub := h.right
    · constructor
      · have: (18:ℚ) < x := by linarith [lb]
        apply Nat.cast_lt.mp this
      · have: x < (24:ℚ) := by linarith [ub]
        apply Nat.cast_lt.mp this
    · constructor
      · have: (18:ℚ) < x := by
          apply Nat.cast_lt.mpr lb
        linarith [this]
      · have: x < (24:ℚ) := by
          apply Nat.cast_lt.mpr ub
        linarith [this]
  -- so natural numbers between 18 and 24 are 19,20,21,22,23
  have h2: {x:ℕ | 18 < x ∧ x < 24} = {19,20,21,22,23} := by
    ext x; simp
    constructor <;> intro h
    · have lb := h.left
      have ub := h.right
      interval_cases x
      all_goals simp
    · rcases h with hh | hh | hh | hh | hh
      <;> rw [hh] <;> simp
  -- so sum over this set is 19+20+21+22+23 = 21x5 = 105
  rw [h1, h2] at hs
  have h3: ({19,20,21,22,23}: Set ℕ) = ↑({19,20,21,22,23}: Finset ℕ) := by
    symm
    exact Set.toFinset_inj.mp rfl
  rw [h3] at hs
  have h4: s = {19,20,21,22,23} := by
    exact Finset.coe_inj.mp hs
  rw [h4]; simp