import Mathlib

theorem algebra_303414 {p q : ℤ} (h : p + q = 1992) (r s : ℕ)
    (hr : r > 0) (hs : s > 0) (hroots : r^2 + p * r + q = 0 ∧ s^2 + p * s + q = 0)
    (hne : r ≠ s) :
    max r s / min r s = 997 := by
-- Unpack the root conditions
  rcases hroots with ⟨hr_eq, hs_eq⟩

  -- Cast to ℤ to do integer arithmetic
  have h1 : (r : ℤ) ^ 2 + p * (r : ℤ) + q = 0 := by
    exact_mod_cast hr_eq
  have h2 : (s : ℤ) ^ 2 + p * (s : ℤ) + q = 0 := by
    exact_mod_cast hs_eq

  -- Subtract the two equations to eliminate q
  have h3 : (r : ℤ) ^ 2 - (s : ℤ) ^ 2 + p * ((r : ℤ) - (s : ℤ)) = 0 := by
    linarith

  -- Factor the expression
  have h4 : ((r : ℤ) - (s : ℤ)) * ((r : ℤ) + (s : ℤ) + p) = 0 := by
    ring_nf at h3 ⊢
    linarith

  -- Use the zero product property
  cases' (mul_eq_zero.mp h4) with h5 h6

  · -- Case 1: r = s, contradiction since r ≠ s
    have : (r : ℤ) = (s : ℤ) := by linarith
    have : r = s := by exact_mod_cast this
    contradiction

  · -- Case 2: r + s + p = 0 ⇒ p = -(r + s)
    have h7 : (r : ℤ) + (s : ℤ) + p = 0 := by linarith
    have hp : p = -(r + s : ℤ) := by linarith

    -- Plug into p + q = 1992 to solve for q
    have hq : q = 1992 + (r + s : ℤ) := by 
      rw [hp] at h
      linarith

    -- Substitute back into the root equation for r
    rw [hp, hq] at h1

    -- Manipulate equation to get the factored form
    have eq3 : ((r : ℤ) - 1) * ((s : ℤ) - 1) = 1993 := by
      nlinarith

    have h6 : (r : ℤ) > 0 := by exact_mod_cast hr
    have h7 : (s : ℤ) > 0 := by exact_mod_cast hs

    have h8 : (r : ℤ) - 1 ∣ 1993 := by 
      use (s : ℤ) - 1
      linarith [eq3]

    have h9 : (r : ℤ) - 1 > 0 := by nlinarith

    have h10 : (r : ℤ) - 1 = 1 ∨ (r : ℤ) - 1 = 1993 := by
      have h14 : (r : ℤ) - 1 ∣ 1993 := h8
      have h13 : (r : ℤ) - 1 ≤ 1993 := by 
        apply Int.le_of_dvd (by norm_num) h14
      interval_cases (r : ℤ) - 1 <;> omega

    cases' h10 with h11 h12

    · -- Case r-1 = 1, so r = 2
      have hr1 : (r : ℤ) = 2 := by linarith
      have hs1 : (s : ℤ) = 1994 := by
        nlinarith [eq3]

      have hr2 : r = 2 := by exact_mod_cast hr1
      have hs2 : s = 1994 := by exact_mod_cast hs1

      rw [hr2, hs2]
      norm_num

    · -- Case r-1 = 1993, so r = 1994
      have hr1 : (r : ℤ) = 1994 := by linarith
      have hs1 : (s : ℤ) = 2 := by
        nlinarith [eq3]

      have hr2 : r = 1994 := by exact_mod_cast hr1
      have hs2 : s = 2 := by exact_mod_cast hs1

      rw [hr2, hs2]
      norm_num