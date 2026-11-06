import Mathlib

/- For $(x,y)$, positive integers, let  $10xy+14x+15y=166$.  Find $x+y$. -/
theorem algebra_20991 {x y : ℕ} (hx : 0 < x) (hy : 0 < y)
    (h : 10 * x * y + 14 * x + 15 * y = 166) : x + y = 6 := by
    -- transform the equation
    replace h : (2 * x + 3) * (5 * y + 7) = 187 := by linarith
    -- factorize 187
    have h0 : Nat.divisors 187 = {1, 11, 17, 187} := by native_decide
    -- 2 * x + 3 is a divisor of 187
    have h1 : 2 * x + 3 ∣ 187 := by
        rw [←h]
        apply dvd_mul_right _ _
    -- lemma: 2 * x + 3 ≤ 187
    have h2 : 2 * x + 3 ≤ 187 := Nat.le_of_dvd (by norm_num) h1
    -- 2 * x + 3 belongs to {1, 11, 17, 187}
    replace h1 : 2 * x + 3 ∈ Nat.divisors 187 := by
        simp [Nat.divisors]
        refine ⟨(by linarith), h1⟩
    -- then we have 2 * x + 3 = 11 ∨ 2 * x + 3 = 17 ∨ 2 * x + 3 = 187
    replace h1 : 2 * x = 8 ∨ 2 * x = 14 ∨ 2 * x = 184 := by
        rw [h0] at h1
        simp at h1
        exact h1
    -- discuss the three cases
    rcases h1 with (h1 | h1 | h1)
    .   -- x = 4
        rw [h1] at h
        -- then y = 2
        replace h : y = 2 := by nlinarith
        linarith
    .   -- x = 7
        rw [h1] at h
        -- contradiction
        replace h : 5 * y = 4 := by nlinarith
        linarith
    .   -- x = 92
        rw [h1] at h
        -- have 5 * y = 183
        replace h : 5 * y = 183 := by nlinarith
        -- for natural numbers, this is impossible
        have h3 : y < 37 := by nlinarith
        linarith
