import Mathlib


/- 5. If two integers $x, y$ satisfy the equation
$$
(2 x+9 y)^{2006}+(4 x-y)^{2006}=7777^{m} \text {, (1) }
$$

then the array $(x, y)$ is called an integer solution of equation (1).
The number of integer solutions of equation (1) is ( ).
(A) 0
(B) 1
(C) 2
(D) 2006 -/
theorem theorem_algebra_316155 (m : ℕ) :
    IsEmpty {(x, y) : ℤ × ℤ |
      (2 * x + 9 * y) ^ 2006 + (4 * x - y) ^ 2006 = 7777 ^ m} := by

  -- 2x+9y and 4x-y have same parity
  have parity_cases (x y:ℤ):
    (Even (2*x+9*y) ∧ Even (4*x-y)) ∨
    (Odd (2*x+9*y) ∧ Odd (4*x-y)) := by
    have h1: Even (2*x) := even_two_mul x
    have h2: Even (4*x) := by
      refine Even.mul_right ?_ x
      exact Int.even_iff.mpr rfl
    by_cases hy: Odd y
    · right
      have h3: Odd (9*y) := by
        clear * - hy
        refine Odd.mul ?_ hy
        exact Int.odd_iff.mpr rfl
      exact ⟨h1.add_odd h3, h2.sub_odd hy⟩
    · left
      rw [Int.not_odd_iff_even] at hy
      have h3: Even (9*y) := hy.mul_left _
      exact ⟨h1.add h3, h2.sub hy⟩

  -- therefore cannot be the case (2x+9y)^2006 + (4x-y)^2006 = 7777^m.
  -- since right side is odd but left always even.
  have not_eq {x y: ℤ} {n:ℕ} (hn: n ≠ 0):
    ¬ (2*x+9*y)^n + (4*x-y)^n = 7777^m := by
    have h1: Odd (7777:ℤ) := Int.odd_iff.mpr rfl
    replace h1: Odd (7777^m: ℤ) := h1.pow
    rintro heq
    rw [← heq] at h1
    absurd h1
    rw [Int.not_odd_iff_even]
    obtain (⟨h2, h3⟩ | ⟨h2,h3⟩) := parity_cases x y
    · replace h2: Even ((2*x+9*y)^n) := by
        rw [Int.even_pow]
        exact ⟨h2, hn⟩
      replace h3: Even ((4*x-y)^n) := by
        rw [Int.even_pow]
        exact ⟨h3, hn⟩
      apply h2.add h3
    · replace h2: Odd ((2*x+9*y)^n) := h2.pow
      replace h3: Odd ((4*x-y)^n) := h3.pow
      apply h2.add_odd h3

  -- so the set is empty.
  by_contra!
  rw [not_isEmpty_iff] at this
  rcases this with ⟨⟨x,y⟩, h⟩
  simp only [Set.mem_setOf_eq] at h
  absurd h
  apply not_eq (by norm_num)