import Mathlib

/- Positive integers $a$, $b$, $c$, and $d$ satisfy $a > b > c > d$, $a + b + c + d = 2010$,
and $a^2 - b^2 + c^2 - d^2 = 2010$. Find the number of possible values of $a$. -/
theorem algebra_94516 : Set.ncard {a : ℤ | ∃ b c d, a > b ∧ b > c ∧ c > d ∧ d > 0 ∧ a + b + c + d = 2010 ∧ a^2 - b^2 + c^2 - d^2 = 2010} = 501 := by
  -- Let $S$ be the set of possible values of $a$. We will show that the standard inclusion
  -- $f : ℕ → ℤ$ is an injection into $S$ from the set ${ a : ℕ | 504 ≤ a ≤ 1004 }$.
  let S := {a : ℤ | ∃ b c d, a > b ∧ b > c ∧ c > d ∧ d > 0 ∧ a + b + c + d = 2010 ∧ a^2 - b^2 + c^2 - d^2 = 2010}
  let f (a : ℕ) := (a : ℤ)

  have hfinj: Set.InjOn f (Set.Icc 504 1004) := by
    intro a ha b hb h
    exact Int.ofNat_inj.mp h

  have hfimage: S = f '' (Set.Icc 504 1004) := by
    ext a
    simp_rw [Set.mem_image, Set.mem_Icc]
    refine ⟨?_, ?_⟩
    . intro ha
      rcases ha with ⟨b, c, d, hab, hbc, hcd, hd, h1, h2⟩
      -- The key step is to factor $a^2 - b^2 + c^2 - d^2 = a + b + c + d$ using
      -- difference-of-squares, and combine this with the inqualities above.
      have : a^2 - b^2 + c^2 - d^2 = a + b + c + d := by simp [h1, h2]
      have : (a + b) * (a - b) + (c + d) * (c - d) - (a + b) - (c + d) = 0 := by linarith
      have eq1 : (a + b) * (a - b - 1) + (c + d) * (c - d - 1) = 0 := by linarith
      -- Some bounds on the terms
      have : a + b > 0 := by linarith
      have : a - b - 1 ≥ 0 := by linarith
      have : c + d > 0 := by linarith
      have : c - d - 1 ≥ 0 := by linarith
      -- Both the terms in the expression are ≥ 0, so since their sum is 0 they must be 0 too.
      have h3 : (a + b) * (a - b - 1) = 0 := by_contradiction fun h => by
        have : 0 < (a + b) * (a - b - 1) + (c + d) * (c - d - 1) := by positivity
        rw [eq1] at this
        exact (Int.lt_irrefl 0 this)
      have h4 : (c + d) * (c - d - 1) = 0 := by_contradiction fun h => by
        have : 0 < (a + b) * (a - b - 1) + (c + d) * (c - d - 1) := by positivity
        rw [eq1] at this
        exact (Int.lt_irrefl 0 this)
      -- This gives us that $a$ and $b$ are consecutive (and similarly for $c$ and $d$).
      have : a = b + 1 := by
        cases Int.mul_eq_zero.mp h3
        . exfalso; linarith
        . linarith
      have : c = d + 1 := by
        cases Int.mul_eq_zero.mp h4
        . exfalso; linarith
        . linarith
      -- Combined with the hypotheses, this gives us the required bounds on $a$.
      have : 2 * a + 2 * c - 2 = 2010 := by linarith
      have : a + c = 1006 := by linarith
      have : 2 ≤ c := by linarith
      have : c ≤ a - 2 := by linarith
      have ha1 : 504 ≤ a := by linarith
      have ha2 : a ≤ 1004 := by linarith
      -- Finally, we can assemble the pieces to show that $a$ is in the image of $f$.
      let x : ℕ := Int.toNat a
      have hx1 : 504 ≤ x := by simp [x, Int.le_toNat (by positivity), ha1]
      have hx2 : x ≤ 1004 := by simp [x, ha2]
      have hx3 : x = a := Int.toNat_of_nonneg (by positivity)
      exact ⟨x, ⟨hx1, hx2⟩, hx3⟩
    . intro ha
      rcases ha with ⟨x, ⟨hx1, hx2⟩, hx3⟩
      -- For the reverse direction, we can essentially reverse the steps above.
      let b := a - 1
      let c := 1006 - a
      let d := c - 1
      have ha1 : 504 ≤ a := by rw [← hx3]; simp [f, hx1]
      have ha2 : a ≤ 1004 := by rw [← hx3]; simp [f, hx2]
      have hab : a > b := by simp [b, c, d]
      have hbc : b > c := by simp [b, c, d]; linarith
      have hcd : c > d := by simp [b, c, d]
      have hd : d > 0 := by simp [b, c, d]; linarith
      have h1 : a + b + c + d = 2010 := by simp [b, c, d]; ring
      have h2 : a^2 - b^2 + c^2 - d^2 = 2010 := by simp [b, c, d]; ring
      exact ⟨b, c, d, hab, hbc, hcd, hd, h1, h2⟩

  -- Thus, the cardinalities of the two sets are the same, namely $501$.
  calc
    S.ncard = (f '' Set.Icc 504 1004).ncard := by rw [hfimage]
    _ = (Set.Icc 504 1004).ncard := by exact Set.ncard_image_of_injOn hfinj
    _ = Nat.card (Set.Icc 504 1004) := by rw [Set.Nat.card_coe_set_eq]
    _ = 501 := by simp