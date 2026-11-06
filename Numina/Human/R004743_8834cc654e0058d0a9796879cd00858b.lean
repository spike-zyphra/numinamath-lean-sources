import Mathlib
/- 30. Solve the system of equations
$$
\begin{array}{l}
2 y=x+\frac{17}{x}, 2 z=y+\frac{17}{y} \quad 2 w=z+\frac{17}{z}, \\
2 x=w+\frac{17}{w}
\end{array}
$$

The number of real solutions $(x, y, z, w)$ is
(A) 1 ; (B) 2 ; (C) 4 ; (D) 8 ; (E) 16 . -/
theorem algebra_314830 : {(x, y, z, w) : ℝ × ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w ≠ 0 ∧ 2 * y = x + 17 / x ∧ 2 * z = y + 17 / y ∧ 2 * w = z + 17 / z ∧ 2 * x = w + 17 / w}.ncard = 2:= by
  -- First, we prove that the solution set consists of exactly two solutions: (√17, √17, √17, √17) and (-√17, -√17, -√17, -√17)
  have h1 : {(x, y, z, w) : ℝ × ℝ × ℝ × ℝ | x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 ∧ w ≠ 0 ∧ 2 * y = x + 17 / x ∧ 2 * z = y + 17 / y ∧ 2 * w = z + 17 / z ∧ 2 * x = w + 17 / w} = {(√17, √17, √17, √17), (-√17, -√17, -√17, -√17)}:= by
    ext ⟨x, y, z, w⟩
    constructor
    .
      -- Forward direction: if (x,y,z,w) satisfies the system, then it's one of the two solutions
      intro h
      simp at h
      rcases h with ⟨g1, g2, g3, g4, h1, h2, h3, h4⟩
      -- Since x ≠ 0, either x < 0 or x > 0
      have g : x < 0 ∨ x > 0:= by exact lt_or_gt_of_ne g1
      -- We prove that all variables have the same sign
      replace g : x > 0 ∧ y > 0 ∧ z > 0 ∧ w > 0 ∨ x < 0 ∧ y < 0 ∧ z < 0 ∧ w < 0:= by
        rcases g with g | g
        .
          -- Case: x < 0. We show this leads to all variables being negative
          set X:= -x with hX
          set Y:= -y with hY
          set Z:= -z with hZ
          set W:= -w with hW
          clear_value X Y Z W
          replace hX : x = -X:= by linarith
          replace hY : y = -Y:= by linarith
          replace hZ : z = -Z:= by linarith
          replace hW : w = -W:= by linarith
          replace g : X > 0:= by linarith
          subst x y z w
          ring_nf at h1 h2 h3 h4
          -- Transform the equations in terms of positive variables X, Y, Z, W
          replace h1 : Y = 1 / 2 * (X + 17 / X):= by
            ring_nf
            linarith
          replace h2 : Z = 1 / 2 * (Y + 17 / Y):= by
            ring_nf
            linarith
          replace h3 : W = 1 / 2 * (Z + 17 / Z):= by
            ring_nf
            linarith
          -- Show that Y, Z, W are all positive
          replace h1 : Y > 0:= by
            rw [h1]
            positivity
          replace h2 : Z > 0:= by
            rw [h2]
            positivity
          replace h3 : W > 0:= by
            rw [h3]
            positivity
          -- Therefore x, y, z, w are all negative
          right
          refine ⟨by linarith, by linarith, by linarith, by linarith⟩
        .
          -- Case: x > 0. We show this leads to all variables being positive
          replace h1 : 2 * y > 0:= by
            rw [h1]
            positivity
          replace h2 : 2 * z > 0:= by
            rw [h2]
            replace h1 : y > 0:= by linarith
            positivity
          replace h3 : 2 * w > 0:= by
            rw [h3]
            replace h2 : z > 0:= by linarith
            positivity
          left
          refine ⟨by linarith, by linarith, by linarith, by linarith⟩
      -- Key lemma: for positive variables satisfying the system, all must equal √17
      have h : ∀ x y z w : ℝ, x > 0 → y > 0 → z > 0 → w > 0 → 2 * y = x + 17 / x → 2 * z = y + 17 / y → 2 * w = z + 17 / z → 2 * x = w + 17 / w → x = √17 ∧ y = √17 ∧ z = √17 ∧ w = √17:= by
        intro x y z w hx hy hz hw h1 h2 h3 h4
        -- By AM-GM inequality, (x + 17/x)/2 ≥ √17 for x > 0
        have g1 : ∀ x : ℝ, x > 0 → 1 / 2 * (x + 17 / x) ≥ √17:= by
          intro x hx
          suffices x + 17 / x - 2 * √17 ≥ 0 by linarith
          -- This follows from (x - √17)²/x ≥ 0
          rw [show x + 17 / x - 2 * √17 = (x - √17) ^ 2 / x by ring_nf ; field_simp ; ring_nf]
          positivity
        -- Apply the inequality to get lower bounds
        have g2 : y ≥ √17:= by linarith [g1 x hx]
        have g3 : z ≥ √17:= by linarith [g1 y hy]
        have g4 : w ≥ √17:= by linarith [g1 z hz]
        replace g1 : x ≥ √17:= by linarith [g1 w hw]
        -- For x > √17, we have x - 17/x > 0
        have g5 : ∀ x : ℝ, x > √17 → x - 17 / x > 0:= by
          intro x hx
          have hx1 : x > 0:= by linarith [show √17 > 0 by positivity]
          rw [show x - 17 / x = (x - √17) * (x + √17) / x by ring_nf ; field_simp ; ring_nf]
          replace hx : x - √17 > 0:= by linarith
          positivity
        -- Each variable is either equal to √17 or greater than √17
        replace g1 : x = √17 ∨ x > √17:= by exact Or.symm (LE.le.gt_or_eq g1)
        replace g2 : y = √17 ∨ y > √17:= by exact Or.symm (LE.le.gt_or_eq g2)
        replace g3 : z = √17 ∨ z > √17:= by exact Or.symm (LE.le.gt_or_eq g3)
        replace g4 : w = √17 ∨ w > √17:= by exact Or.symm (LE.le.gt_or_eq g4)
        -- Case analysis: if any variable equals √17, then all must equal √17
        rcases g1 with g1 | g1
        .
          -- If x = √17, then y = √17, z = √17, w = √17
          subst x
          field_simp at h1
          replace h1 : y = √17:= by linarith
          subst y
          field_simp at h2
          replace h2 : z = √17:= by linarith
          subst z
          field_simp at h3
          replace h3 : w = √17:= by linarith
          subst w
          simp
        .
          -- If x > √17, we check other variables
          rcases g2 with g2 | g2
          .
            -- If y = √17, then z = √17, w = √17, x = √17 (contradiction)
            subst y
            field_simp at h2
            replace h2 : z = √17:= by linarith
            subst z
            field_simp at h3
            replace h3 : w = √17:= by linarith
            subst w
            field_simp at h4
            replace h4 : x = √17:= by linarith
            subst x
            simp
          .
            rcases g3 with g3 | g3
            .
              -- If z = √17, then w = √17, x = √17, y = √17 (contradiction)
              subst z
              field_simp at h3
              replace h3 : w = √17:= by linarith
              subst w
              field_simp at h4
              replace h4 : x = √17:= by linarith
              subst x
              field_simp at h1
              replace h1 : y = √17:= by linarith
              subst y
              simp
            .
              rcases g4 with g4 | g4
              .
                -- If w = √17, then x = √17, y = √17, z = √17 (contradiction)
                subst w
                field_simp at h4
                replace h4 : x = √17:= by linarith
                subst x
                field_simp at h1
                replace h1 : y = √17:= by linarith
                subst y
                field_simp at h2
                replace h2 : z = √17:= by linarith
                subst z
                field_simp at h3
                replace h3 : w = √17:= by linarith
                subst w
                simp
              .
                -- If all variables are > √17, we get a contradiction
                have g6:= g5 y g2
                have g7:= g5 z g3
                have g8:= g5 w g4
                replace g5:= g5 x g1
                linarith
      -- Apply the cases based on sign
      rcases g with g | g
      .
        -- Case: all variables are positive
        rcases g with ⟨g1, g2, g3, g4⟩
        specialize h x y z w g1 g2 g3 g4 h1 h2 h3 h4
        rcases h with ⟨h1, h2, h3, h4⟩
        subst x y z w
        simp
      .
        -- Case: all variables are negative
        rcases g with ⟨g1, g2, g3, g4⟩
        -- Apply the lemma to the positive versions
        specialize h (-x) (-y) (-z) (-w) (by linarith) (by linarith) (by linarith) (by linarith) (by ring_nf at h1 ⊢ ; linarith) (by ring_nf at h2 ⊢ ; linarith) (by ring_nf at h3 ⊢ ; linarith) (by ring_nf at h4 ⊢ ; linarith)
        rcases h with ⟨h1, h2, h3, h4⟩
        replace h1 : x = -√17:= by linarith
        replace h2 : y = -√17:= by linarith
        replace h3 : z = -√17:= by linarith
        replace h4 : w = -√17:= by linarith
        subst x y z w
        simp
    .
      -- Backward direction: both solutions satisfy the system
      intro h
      simp at h
      rcases h with h | h
      all_goals
        rcases h with ⟨h1, h2, h3, h4⟩
        subst x y z w
        simp
      .
        -- Verify that (√17, √17, √17, √17) satisfies the system
        ring_nf
      .
        -- Verify that (-√17, -√17, -√17, -√17) satisfies the system
        field_simp
        ring_nf
        field_simp
        ring_nf
  -- Use the characterization to compute the cardinality
  rw [h1]
  -- Convert the set to a finset for cardinality computation
  rw [show ({(√17, √17, √17, √17), (-√17, -√17, -√17, -√17)} : Set (ℝ × ℝ × ℝ × ℝ)) = ({(√17, √17, √17, √17), (-√17, -√17, -√17, -√17)} : Finset (ℝ × ℝ × ℝ × ℝ)) by simp]
  rw [Set.ncard_coe_Finset]
  -- Count the elements in the finset
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  -- Show that the two solutions are distinct
  by_contra H
  simp at H
  linarith [show √17 > 0 by positivity]
