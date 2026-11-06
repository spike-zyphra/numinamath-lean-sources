import Mathlib

/- What is the largest integer that must divide the product of any $4$ consecutive integers?-/
theorem number_theory_5529 : IsGreatest {n | ∀ k, n ∣ (k * (k + 1) * (k + 2) * (k + 3))} 24 := by
  -- simplify the expression
  simp [IsGreatest, upperBounds]
  -- split the goal into two parts
  refine ⟨?_, ?_⟩

  . -- prove that 24 divides the product of any 4 consecutive integers
    intro k
    -- induction on k
    induction' k using Nat.strong_induction_on with k ih
    -- case split to (k = 0, 1, 2) or (k > 2)
    by_cases hk2 : k ≤ 2
    . -- case k ≤ 2
      interval_cases k -- case split to k = 0, 1 or 2
      -- trivial decide
      <;> simp [(by decide : 24 ∣ 120)]

    . -- case k > 3
      -- use (k-3)-induction hypothetis
      specialize ih (k - 3) (by omega)
      -- change variable x = k - 3
      let x : ℕ := k - 3
      have hx : k = x + 3 := by omega
      rw [hx] at ih ⊢

      -- split the expression into 3 parts
      -- first part is the induction hypothesis
      have h1 : (x + 3 - 3) * (x + 3 - 3 + 1) * (x + 3 - 3 + 2) * (x + 3 - 3 + 3) =  x * (x + 1) * (x + 2) * (x + 3) := by rw[(by omega : x + 3 - 3 = x)] -- mid step
      -- prove the transformation by expanding the expression
      have h2 : (x + 3) * (x + 3 + 1) * (x + 3 + 2) * (x + 3 + 3) = (x + 3 - 3) * (x + 3 - 3 + 1) * (x + 3 - 3 + 2) * (x + 3 - 3 + 3) + (12* x^3 + 108 *x^2) + 24 * (14 * x + 15) := by
        calc _ = x^4 + 18 *x^3 + 119 *x^2 + 342* x + 360 := by ring
          _ = x^4 + 6* x^3 + 11 *x^2 + 6 *x + 12* x^3 + 108 *x^2 + 336* x + 360 := by ring
          _ = x * (x + 1) * (x + 2) * (x + 3) +  (12* x^3 + 108 *x^2) + 24 * (14 * x + 15):= by ring
          _ = _ := by rw [← h1]

      -- second part uses lemma: 2 ∣ x ^ 3 + x ^ 2
      have h3 : 2 ∣ x ^ 3 + x ^ 2 := by
        by_cases hx2 : x % 2 = 0 -- discuss x is even or odd
        . -- x is even
          rw [(by nlinarith : x ^ 3 + x ^ 2 = x *  (x ^ 2 + x))] -- rewrite the expression
          -- 2 ∣ x
          replace hx2 : 2 ∣ x := by exact Nat.dvd_of_mod_eq_zero hx2
          -- then 2 ∣ x * (x ^ 2 + x)
          apply dvd_mul_of_dvd_left hx2 _
        . -- x is odd
          -- 2 ∣ x + 1
          replace hx2 : x % 2 = 1 := by omega
          replace hx2 : (x + 1) % 2 = 0 := by exact Nat.succ_mod_two_eq_zero_iff.mpr hx2
          replace hx2 : 2 ∣ (x + 1) := by exact Nat.dvd_of_mod_eq_zero hx2
          -- rewrite the expression
          rw [(by nlinarith : x ^ 3 + x ^ 2 = (x + 1) * (x ^ 2))]
          -- then 2 ∣ (x + 1) * (x ^ 2)
          apply dvd_mul_of_dvd_left hx2 _
      -- use the lemma to prove the second part
      have h4 : 24 ∣ 12 * x ^ 3 + 108 * x ^ 2 := by
        rw [(by nlinarith : 12 * x ^ 3 + 108 * x ^ 2 = 12 * (x ^ 3 + x ^ 2) + 24 * (4 * x ^ 2))]
        -- sufficient to prove 24 ∣ 12 * (x ^ 3 + x ^ 2)
        refine dvd_add ?_ (dvd_mul_right _ _)
        -- use h3 to write x ^ 3 + x ^ 2 = 2 * y
        rcases h3 with ⟨y, hy⟩
        -- then trivial
        rw [hy, (by linarith : 12 * (2 * y) = 24 * y)]
        apply dvd_mul_right

      rw [h2]
      -- the 3 parts are all divisible by 24
      refine dvd_add (dvd_add ih h4) (dvd_mul_right 24 _)
  . -- prove that 24 is the greatest integer that must divide the product of any 4 consecutive integers
    -- simplify the statement
    intro a
    intro h
    -- consider the special case k = 1
    specialize h 1
    simp at h
    -- have a ∣ 24 and then a ≤ 24
    apply Nat.le_of_dvd (by decide) h
