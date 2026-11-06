import Mathlib


/- 6,7

The sum of positive numbers $x_{1}, x_{2}, \ldots, x_{n}$ is $1 / 2$. Prove that $\frac{1-x_{1}}{1+x_{1}} \cdot \frac{1-x_{2}}{1+x_{2}} \cdot \ldots \cdot \frac{1-x_{n}}{1+x_{n}} \geq \frac{1}{3}$. -/
theorem inequalities_214153 (n : ℕ) (hn : 0 < n) (x : Fin n → ℝ)
    (hx : ∑ i : Fin n, x i = 1 / 2) (hx' : ∀ i : Fin n, 0 < x i) :
    ∏ i : Fin n, (1 - x i) / (1 + x i) ≥ 1 / 3
  := by
    -- Use ≤
    rw [ge_iff_le]

    -- n is at least 1
    have hn' : 1 ≤ n := by omega

    -- We prove the more general statement, where ∑ i : Fin n, x i = s < 1
    generalize hs : (1 : ℝ) / 2 = s at hx
    have s_lt_one : s < 1 := by
      rw [←hs]
      linarith only

    -- we'll prove (1 - s) / (1 + s) ≤ ∏ i : Fin n, (1 - x i) / (1 + x i)
    convert_to (1 - s) / (1 + s) ≤ ∏ i : Fin n, (1 - x i) / (1 + x i)
    · rw [←hs]
      ring

    -- forget that s = 1 / 2
    clear hs
    -- prove by induction on n, starting on n = 1
    induction' n, hn' using Nat.le_induction with n hh h2 generalizing s
    -- both sides are equal when n = 1
    · rw [Fin.sum_univ_one x] at hx
      rw [Fin.prod_univ_one, hx]
    -- for induction, x will be x_0, .., x_n, and x' will be x_0, .., x_(n-1)
    · let x' := (fun i : Fin n => x (i.castSucc))
      -- s' is the sum of x_0, .., x_(n-1)
      let s' := ∑ i : Fin n, x' i

      -- we prove some bounds
      -- x_n is positive
      have last_pos : 0 < x (Fin.last n) := hx' (Fin.last n)
      -- s' is nonnegative
      have s'_nonnegative : 0 ≤ s' := Fintype.sum_nonneg <| StrongLT.le fun i => hx' i.castSucc
      -- s' < 1
      have s'_lt_one : s' < 1 := by
        -- because s < 1, and s' < s
        rw [Fin.sum_univ_castSucc] at hx
        linarith only [last_pos, hx, s_lt_one]

      -- s is positive
      have s_pos : 0 < s := by
        rw [←hx, Fin.sum_univ_castSucc]
        linarith only [last_pos, s'_nonnegative]

      -- rewrite RHS to apply induction hypothesis
      rw [Fin.prod_univ_castSucc]

      -- we use the induction hypothesis to rewrite the RHS
      have induction_hyp := h2 hh x' (fun i => hx' i.castSucc) s' rfl s'_lt_one
      apply_fun (fun xx => xx * ((1 - x (Fin.last n)) / (1 + x (Fin.last n)))) at induction_hyp
      refine le_trans ?_ induction_hyp

      -- remove s' from goal and combine fractions
      have s'_eq : s' = s - x (Fin.last n) := by
        rw [←hx, Fin.sum_univ_castSucc]
        simp only [add_sub_cancel_right]
      simp only [s'_eq, div_mul_div_comm]
      convert_to (1 - s) / (1 + s) ≤ (1 - s + x (Fin.last n) * (s - x (Fin.last n))) / ( 1 + s + x (Fin.last n) * (s - x (Fin.last n)))
      · ring

      -- express without fractions
      rw [div_le_div_iff₀ (by positivity) (by rw [←s'_eq]; positivity)]
      ring_nf

      -- simplify
      suffices hle : x (Fin.last n) * s * (x (Fin.last n) - s) ≤ x (Fin.last n) * s * (s - x (Fin.last n))
      · linarith only [hle]

      -- remove common factors
      rw [mul_le_mul_left (by positivity)]

      -- use s = s' + x to simplify
      have s_eq : s = s' + x (Fin.last n) := by linarith
      simp only [s_eq, sub_add_cancel_right, add_sub_cancel_right, neg_le_self_iff, ge_iff_le]

      -- we have that 0 ≤ s'
      exact s'_nonnegative

      -- we used that multiplication of non-zero value is monotone
      · intro aa bb cc
        rw [Fin.sum_univ_castSucc] at hx
        apply mul_le_mul_of_nonneg_right cc
        apply div_nonneg
        -- 0 ≤ 1 - x (Fin.last n)
        · linarith
        -- 0 ≤ 1 + x (Fin.last n)
        · positivity