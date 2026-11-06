import Mathlib

/- For any sequence of real numbers $A=(a_1,a_2,a_3,\ldots)$, define $\Delta A$ to be the sequence $(a_2-a_1,a_3-a_2,a_4-a_3,\ldots)$, whose $n^{\text{th}}$ term is $a_{n+1}-a_n$. Suppose that all of the terms of the sequence $\Delta(\Delta A)$ are $1$, and that $a_{19}=a_{92}=0$. Find $a_1$. -/
theorem algebra_20894 {Δ : (ℕ → ℝ) → (ℕ → ℝ)} (hDelta : ∀ i a, Δ a i = a (i + 1) - a i) {a : ℕ → ℝ} (ha1 : a (19 - 1) = 0) (ha2 : a (92 - 1) = 0) (hDeltaa : Δ (Δ a) = 1) : a (1 - 1) = 819 := by
  -- we prove $a_m = (m - 1) m / 2 + a_0 + m (a_1 - a_0)$ by two step induction
  have ameq (m : ℕ) : a m = (m - 1) * m / 2 + a 0 + m * (a 1 - a 0) := by
    let P : ℕ → Prop := by
      intro n
      exact a n = (↑n - 1) * ↑n / 2 + a 0 + ↑n * (a 1 - a 0)
    have H1 : P 0 := by
      simp only [CharP.cast_eq_zero, zero_sub, mul_zero, zero_div, zero_add, zero_mul, add_zero, P]
    have H2 : P 1 := by
      simp only [Nat.cast_one, sub_self, mul_one, zero_div, zero_add, one_mul, add_sub_cancel, P]
    have H3 : (n : ℕ) → P n → P n.succ → P n.succ.succ := by
      intro n Pn Pns 
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, P]
      simp only [P] at Pn
      simp only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, add_sub_cancel_right, P] at Pns
      have eq : Δ (Δ a) n = 1 := by
        exact congrFun hDeltaa n
      simp only [hDelta] at eq
      apply eq_add_of_sub_eq at eq
      apply eq_add_of_sub_eq at eq
      rw [eq, Pn, Pns]
      ring
    show P m
    exact Nat.twoStepInduction H1 H2 H3 m
  -- solving $a_18 = a_91 = 0$ we get $a_0 = 819$
  have a19eq := ameq (19 - 1)
  rw [ha1] at a19eq
  have a92eq := ameq (92 - 1)
  rw [ha2] at a92eq
  rw [Nat.sub_self]
  ring_nf at a19eq
  ring_nf at a92eq
  linarith