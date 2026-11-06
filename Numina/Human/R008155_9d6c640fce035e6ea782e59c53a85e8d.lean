import Mathlib

/- If the system of equations

$$
\begin{aligned}
& |x+y|=99 \\
& |x-y|=c
\end{aligned}
$$

has exactly two real solutions $(x, y)$, find the value of $c$.-/
theorem algebra_611245 :
    {c : ℝ | {(x, y) : ℝ × ℝ | |x + y| = 99 ∧ |x - y| = c}.encard = 2} = {0} := by
  -- Simplify the goal into two parts.
  ext c
  rw [Set.mem_setOf]
  -- Let S = {x, y | |x + y| = 99 and |x - y| = c}.
  let S := {(x, y) : ℝ × ℝ | |x + y| = 99 ∧ |x - y| = c}
  -- Show that if c < 0, the system has no solution.
  have h₀ : c < 0 → S.encard = 0 := by
    intro hc
    simp [S]
    ext ⟨x, y⟩
    simp [Set.mem_setOf]
    intro _
    -- A contradiction is derived because |x - y| ≥ 0 > c.
    rw [<-ne_eq]
    apply LT.lt.ne'
    exact hc.trans_le (by positivity)
  -- Show that if c = 0, the system has exactly two solutions.
  have h₁ : c = 0 → S.encard = 2 := by
    intro hc
    -- It suffices to show that S = {(-99 / 2, -99 / 2), (99 / 2, 99 / 2)}.
    suffices S = {(-99 / 2, -99 / 2), (99 / 2, 99 / 2)} by
      rw [this, show ({(-99 / 2, -99 / 2), (99 / 2, 99 / 2)} : Set (ℝ × ℝ)) = ({(-99 / 2, -99 / 2), (99 / 2, 99 / 2)} : Finset (ℝ × ℝ)) by simp, Set.encard_coe_eq_coe_finsetCard]
      norm_num
    ext ⟨x, y⟩
    simp [Set.mem_setOf, S]
    apply Iff.intro
    . -- Show that if |x + y| = 99 and |x - y| = c, then (x, y) = (-99 / 2, -99 / 2) or (99 / 2, 99 / 2).
      rintro ⟨h₁, h₂⟩
      -- Note that |x + y| = 99 implies x + y = 99 or x + y = -99.
      rw [abs_eq (by norm_num)] at h₁
      -- Note that |x - y| = 0 implies x = y.
      simp [hc] at h₂
      -- Solve the system of equations.
      cases h₁ with
      | inl h₁ =>
        -- If x + y = 99, then x = y = 99 / 2.
        right
        exact ⟨by linarith, by linarith⟩
      | inr h₁ =>
        -- If x + y = -99, then x = y = -99 / 2.
        left
        exact ⟨by linarith, by linarith⟩
    . -- Show that if (x, y) = (-99 / 2, -99 / 2) or (99 / 2, 99 / 2), then |x + y| = 99 and |x - y| = c.
      intro h
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
      all_goals
        subst x y c
        simp
  -- Show that if c > 0, the system has four solutions.
  have h₂ : c > 0 → S.encard = 4 := by
    intro hc
    -- It suffices to show that S = {((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), ((99 + c) / 2, (99 - c) / 2)}.
    suffices S = {((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), ((99 + c) / 2, (99 - c) / 2)} by
      rw [this, show ({((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), ((99 + c) / 2, (99 - c) / 2)} : Set (ℝ × ℝ)) = ({((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), ((99 + c) / 2, (99 - c) / 2)} : Finset (ℝ × ℝ)) by simp, Set.encard_coe_eq_coe_finsetCard]
      iterate 3 rw [Finset.card_insert_of_not_mem]
      -- Verify that the four solutions are distinct.
      . simp
      . simp
        intro this
        linarith only [hc, this]
      . rw [<-Finset.forall_mem_not_eq]
        simp
        refine ⟨?_, ?_⟩
        all_goals
          intro this
          linarith only [hc, this]
      . rw [<-Finset.forall_mem_not_eq]
        simp
        refine ⟨?_, ?_, ?_⟩
        all_goals
          intro this
          linarith only [hc, this]
    ext ⟨x, y⟩
    simp [Set.mem_setOf, S]
    apply Iff.intro
    . -- Show that if |x + y| = 99 and |x - y| = c, then (x, y) = ((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), or ((99 + c) / 2, (99 - c) / 2).
      rintro ⟨h₁, h₂⟩
      -- Note that |x + y| = 99 implies x + y = 99 or x + y = -99.
      rw [abs_eq (by norm_num)] at h₁
      -- Note that |x - y| = c implies x - y = c or x - y = -c.
      rw [abs_eq (by positivity)] at h₂
      -- Solve the system of equations.
      cases h₁ with
      | inl h₁ =>
        cases h₂ with
        | inl h₂ =>
          -- If x + y = 99 and x - y = c, then x = (99 + c) / 2 and y = (99 - c) / 2.
          iterate 3 right
          exact ⟨by linarith, by linarith⟩
        | inr h₂ =>
          -- If x + y = 99 and x - y = -c, then x = (99 - c) / 2 and y = (99 + c) / 2.
          iterate 2 right
          left
          exact ⟨by linarith, by linarith⟩
      | inr h₁ =>
        cases h₂ with
        | inl h₂ =>
          -- If x + y = -99 and x - y = c, then x = (-99 - c) / 2 and y = (-99 + c) / 2.
          right
          left
          exact ⟨by linarith, by linarith⟩
        | inr h₂ =>
          -- If x + y = -99 and x - y = -c, then x = (-99 + c) / 2 and y = (-99 - c) / 2.
          left
          exact ⟨by linarith, by linarith⟩
    . -- Show that if (x, y) = ((-99 - c) / 2, (-99 + c) / 2), ((-99 + c) / 2, (-99 - c) / 2), ((99 - c) / 2, (99 + c) / 2), or ((99 + c) / 2, (99 - c) / 2), then |x + y| = 99 and |x - y| = c.
      intro h
      obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := h
      all_goals
        subst x y
        ring_nf
        simp [le_of_lt hc]
  -- Now we can return to the goal and shows that S.encard = 2 iff c = 0.
  rw [show {(x, y) : ℝ × ℝ | |x + y| = 99 ∧ |x - y| = c} = S by rfl]
  simp
  apply Iff.intro
  . intro h
    by_contra!
    rw [ne_eq] at this
    apply lt_or_gt_of_ne at this
    obtain this | this := this
    all_goals
      first | apply h₀ at this | apply h₂ at this
      replace this := (this.symm) ▸ h
      norm_num at this
  . exact h₁
