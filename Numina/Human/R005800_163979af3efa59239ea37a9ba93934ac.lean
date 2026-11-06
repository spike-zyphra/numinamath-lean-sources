import Mathlib
/- For any real number $\alpha$, define

$$
\operatorname{sign}(\alpha)= \begin{cases}+1 & \text { if } \alpha>0 \\ 0 & \text { if } \alpha=0 \\ -1 & \text { if } \alpha<0\end{cases}
$$

How many triples $(x, y, z) \in \mathbb{R}^{3}$ satisfy the following system of equations

$$
\begin{aligned}
& x=2018-2019 \cdot \operatorname{sign}(y+z) \\
& y=2018-2019 \cdot \operatorname{sign}(z+x) \\
& z=2018-2019 \cdot \operatorname{sign}(x+y) ?
\end{aligned}
$$ -/
theorem algebra_609979 (sgn : ℝ → ℝ) (hsgn : sgn = fun x => if x > 0 then 1 else (if x < 0 then -1 else 0)) : {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * sgn (y + z) ∧ y = 2018 - 2019 * sgn (z + x) ∧ z = 2018 - 2019 * sgn (x + y)}.ncard = 3:= by

  -- Prove that the solution set equals {(-1,-1,4037), (-1,4037,-1), (4037,-1,-1)}
  have h1 : {(x, y, z) : ℝ × ℝ × ℝ | x = 2018 - 2019 * sgn (y + z) ∧ y = 2018 - 2019 * sgn (z + x) ∧ z = 2018 - 2019 * sgn (x + y)} = {(-1, -1, 4037), (-1, 4037, -1), (4037, -1, -1)}:= by
    ext ⟨x, y, z⟩

    -- Helper lemma: if x > 0, then sgn(x) = 1
    have g1 : ∀ x : ℝ, x > 0 → sgn x = 1:= by
      intro x hx
      simp [hsgn, hx]

    -- Helper lemma: if x < 0, then sgn(x) = -1
    have g2 : ∀ x : ℝ, x < 0 → sgn x = -1:= by
      intro x hx
      simp [hsgn, hx]
      intro h
      by_contra _
      linarith

    -- The proof splits into forward (⊆) and backward (⊇) directions
    constructor
    .
      -- Forward direction: prove that any solution must be one of the three points (-1,-1,4037), (-1,4037,-1), or (4037,-1,-1)
      intro h
      simp at h
      rcases h with ⟨h1, h2, h3⟩

      -- First prove that in any solution, x + y cannot be zero
      -- This is crucial because if x + y were zero, it would lead to a contradiction
      have h4 : ∀ x y z : ℝ, x = 2018 - 2019 * sgn (y + z) ∧ y = 2018 - 2019 * sgn (z + x) ∧ z = 2018 - 2019 * sgn (x + y) → x + y ≠ 0:= by
        intro x y z h
        rcases h with ⟨h1, h2, h3⟩
        -- Prove that x can only take values -1, 2018, or 4037
        have h5 : ∀ x y z : ℝ, x = 2018 - 2019 * sgn (y + z) ∧ y = 2018 - 2019 * sgn (z + x) ∧ z = 2018 - 2019 * sgn (x + y) → x = -1 ∨ x = 2018 ∨ x = 4037:= by
          intro x y z h
          rcases h with ⟨h1, h2, h3⟩
          -- Case analysis on whether y + z = 0
          by_cases h4 : y + z = 0
          .
            rw [h4] at h1
            simp [hsgn] at h1
            simp [h1]
          .
            replace h4 : y + z < 0 ∨ y + z > 0:= by exact lt_or_gt_of_ne h4
            rcases h4 with h4 | h4
            .
              have h5 : sgn (y + z) = -1:= by
                simp [hsgn, h4]
                intro h5
                by_contra _
                linarith
              rw [h5] at h1
              ring_nf at h1
              simp [h1]
            .
              simp [hsgn, h4] at h1
              ring_nf at h1
              simp [h1]
        have g1:= h5 x y z ⟨h1, h2, h3⟩
        have g2:= h5 y z x ⟨h2, h3, h1⟩
        rcases g1 with g1 | g1 | g1
        all_goals
          rcases g2 with g2 | g2 | g2
          all_goals
            rw [g1, g2]
            norm_num
      have h5:= h4 y z x ⟨h2, h3, h1⟩
      have h6:= h4 z x y ⟨h3, h1, h2⟩
      replace h4:= h4 x y z ⟨h1, h2, h3⟩
      replace h5 : y + z < 0 ∨ y + z > 0:= by exact lt_or_gt_of_ne h5
      replace h6 : z + x < 0 ∨ z + x > 0:= by exact lt_or_gt_of_ne h6
      replace h4 : x + y < 0 ∨ x + y > 0:= by exact lt_or_gt_of_ne h4
      rcases h4 with h4 | h4
      .
        rw [g2 (x + y) h4] at h3
        ring_nf at h3
        rcases h5 with h5 | h5
        .
          rw [g2 (y + z) h5] at h1
          ring_nf at h1
          rw [g1 (z + x) (by linarith)] at h2
          ring_nf at h2
          by_contra _
          linarith
        .
          rw [g1 (y + z) (by linarith)] at h1
          ring_nf at h1
          rw [g1 (z + x) (by linarith)] at h2
          ring_nf at h2
          subst x y z
          simp
      .
        rw [g1 (x + y) h4] at h3
        ring_nf at h3
        rcases h5 with h5 | h5
        .
          rw [g2 (y + z) h5] at h1
          ring_nf at h1
          rw [g1 (z + x) (by linarith)] at h2
          ring_nf at h2
          subst x y z
          simp
        .
          rw [g1 (y + z) h5] at h1
          ring_nf at h1
          rw [g2 (z + x) (by linarith)] at h2
          ring_nf at h2
          subst x y z
          simp
    .
      -- Backward direction: verify that each of the three points satisfies the system
      intro h
      simp at h
      rcases h with h | h | h
      .
        -- Case 1: (-1, -1, 4037)
        rcases h with ⟨h1, h2, h3⟩
        simp
        rw [g1 (y + z) (by linarith)]
        rw [g1 (z + x) (by linarith)]
        rw [g2 (x + y) (by linarith)]
        subst x y z
        norm_num
      .
        rcases h with ⟨h1, h2, h3⟩
        simp
        rw [g2 (z + x) (by linarith)]
        rw [g1 (x + y) (by linarith)]
        rw [g1 (y + z) (by linarith)]
        subst x y z
        norm_num
      .
        rcases h with ⟨h1, h2, h3⟩
        simp
        rw [g1 (x + y) (by linarith)]
        rw [g2 (y + z) (by linarith)]
        rw [g1 (z + x) (by linarith)]
        subst x y z
        norm_num
  rw [h1]
  rw [show ({(-1, -1, 4037), (-1, 4037, -1), (4037, -1, -1)} : Set (ℝ × ℝ × ℝ)) = ({(-1, -1, 4037), (-1, 4037, -1), (4037, -1, -1)} : Finset (ℝ × ℝ × ℝ)) by simp]
  rw [Set.ncard_coe_Finset]
  repeat rw [Finset.card_insert_of_not_mem]
  simp
  all_goals
    by_contra H
    simp at H
    norm_num at H
