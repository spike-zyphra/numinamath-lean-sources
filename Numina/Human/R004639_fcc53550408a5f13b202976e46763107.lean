import Mathlib

/-
Problem 4. Find all pairs $(x, y)$ of integer numbers such that $x^{3}=$ $y^{3}+2 y^{2}+1$. Nikolay Nikolov and Emil Kolev
 -/
theorem number_theory_292445 (x y : ℤ) :
    x^3 = y^3 + 2 * y^2 + 1 ↔ (x = -2 ∧ y = -3) ∨ (x = 1 ∧ y = -2) ∨ (x = 1 ∧ y = 0) := by
  constructor
  -- show that x^3 = y^3 + 2 * y^2 + 1 implies that (x, y) = (-2, -3), (1, -2), or (1, 0)
  · intro h
    -- f(x) = x ^ 3 is a strictly monotone function
    have pow3 := @Odd.strictMono_pow ℤ _ 3 _ (by decide)
    -- if x ^ 3 < y ^ 3 then x < y
    have lt3 {x y : ℤ} (h : x ^ 3 < y ^ 3) : x < y := by
      exact (StrictMono.lt_iff_lt pow3).mp h
    -- if x ^ 3 = y ^ 3 then x = y
    have eq3 {x y : ℤ} (h : x ^ 3 = y ^ 3) : x = y := by
      apply eq_of_le_of_le
      · contrapose! h
        exact ne_of_gt (pow3 h)
      · contrapose! h
        exact ne_of_lt (pow3 h)
    -- show that y + 1 ≤ x
    have hx : y + 1 ≤ x := by
      -- suppose that x ≤ y and show that x ^ 3 < y ^ 3 + 2 * y ^ 2 + 1,
      contrapose! h
      apply ne_of_lt
      -- we have x ^ 3 ≤ y ^ 3 < y ^ 3 + 2 * y ^ 2 + 1 since 2 * y ^ 2 + 1 > 0
      apply lt_of_le_of_lt (b := y ^ 3)
      · exact pow3.monotone (by omega)
      · nlinarith
    -- now show that y * (y + 3) ≤ 0
    -- we have
    -- y * (y + 3) = (y + 1) ^ 3 - (y ^ 3 + 2 * y ^ 2 + 1)
    --             = (y + 1) ^ 3 - x ^ 3
    -- we know that y + 1 ≤ x so y * (y + 3) ≤ 0
    have hy : y * (y + 3) ≤ 0 := calc
      y * (y + 3) = (y + 1) ^ 3 - (y ^ 3 + 2 * y ^ 2 + 1) := by ring
      _ = (y + 1) ^ 3 - x ^ 3 := by rw [←h]
      _ ≤ 0 := by
          rw [sub_nonpos]
          exact pow3.monotone hx
    rw [mul_nonpos_iff] at hy
    -- we have 2 cases 0 ≤ y, y + 3 ≤ 0 or y ≤ 0, 0 ≤ y + 3
    -- the first case is impossible
    cases' hy with hy hy
    · omega
    · have ⟨y1, y2⟩ : -3 ≤ y ∧ y ≤ 0 := by omega
      -- we have -3 ≤ y ≤ 0, so y = -3, -2, -1, or 0
      interval_cases y <;> norm_num at h
      -- if y = -3 then x^3 = -8 which implies that x = -2
      · rw [show -8 = (-2)^3 by norm_num] at h
        simp [eq3 h]
      -- if y = -2 then x^3 = 1 which implies that x = 1
      · rw [show 1 = (1 : ℤ)^3 by norm_num] at h
        simp [eq3 h]
      -- if y = -1 then we have x ^ 3 = 2 which is impossible
      · have h1 := lt3 (show 1 ^ 3 < x ^ 3 by omega)
        have h2 := lt3 (show x ^ 3 < 2 ^ 3 by omega)
        omega
      -- if y = 0 then x^3 = 1 which implies that x = 1
      · rw [show 1 = (1 : ℤ)^3 by norm_num] at h
        simp [eq3 h]
  -- verify that (x, y) = (-2, -3), (1, -2), or (1, 0) satisfy the equality
  · intro h
    rcases h with h | h | h <;> simp [h]