import Mathlib

/- If $$\begin{array}{@{}l@{\;}l@{}l@{}l} && & P_b \\ & \times & & P_b \\ \cline{2-4} & & 3 & 1_b, \\ \end{array} $$where $P$ and $b$ represent two distinct digits 0-9 and $P$ is one less than $b$, what is the value of the base $b$? -/
theorem number_theory_18620 {P b : ℕ} (hb : 3 < b) (hP : P < b) (hP1 : P + 1 = b)
    (h : Nat.digits b (P * P) = [1, 3]) :
    b = 5 := by
  -- $P = b - 1$
  have Peq : P = b - 1 := by exact Nat.eq_sub_of_add_eq hP1
  -- $P \cdot P = 3 \cdot b + 1$
  have Psqeq : P * P = 3 * b + 1 := by
    rw [Nat.digits_of_two_le_of_pos, Nat.digits_of_lt] at h
    -- $P \cdot P % b = 3$ and $P \cdot P / b = 1$
    simp only [List.cons.injEq, and_true] at h
    rw [← h.1, ← h.2]
    -- $P \cdot P = P \cdot P % b + b \cdot (P \cdot P / b)$
    exact Eq.symm (Nat.div_add_mod' (P * P) b)
    -- $P \cdot P / b \neq 0$
    apply (Nat.div_ne_zero_iff).mpr
    -- suffices to show $b \neq 0$ and $b \leq P * P$
    refine ⟨Nat.not_eq_zero_of_lt hb, ?_⟩
    rw [Peq]
    nlinarith
    -- $P * P / b < b$
    refine (Nat.div_lt_iff_lt_mul ?_).mpr ?_
    any_goals
    nlinarith
  -- $P * P = 3 * (P + 1) + 1$, so $P = 4, b = 5$
  rw [← hP1] at Psqeq
  nlinarith
