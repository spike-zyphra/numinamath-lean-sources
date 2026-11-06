import Mathlib

/-A number is divisible by $9$ if the sum of its digits is divisible by $9.$ For example, the number $19\,836$ is divisible by $9$ but $19\,825$ is not.

If $D\,767\,E89$ is divisible by $9,$ where $D$ and $E$ each represent a single digit, what is the sum of all possible values of the sum $D+E?$-/
theorem number_theory_15524 (D E : ℕ) (hD : D < 10) (hE : E < 10)
    (h : 9 ∣ Nat.ofDigits 10 [9, 8, E, 7, 6, 7, D]):
    (D + E = 8 ∨ D + E = 17) ∧ 8 + 17 = 25 := by
  -- For $D\,767\,E89$ to be divisible by $9,$ we must have $$D+7+6+7+E+8+9 = 37+D+E$$ divisible by $9.
  have h: 9 ∣ (37 + D + E) := by
    by_cases hD₀: D = 0
    . -- Nat.digits_ofDigits don't allow the first digit to be $0.$
      -- But, `D = 0` won't cause a problem for our proof.
      rw [hD₀] at h
      have : Nat.ofDigits 10 [9, 8, E, 7, 6, 7, 0] = Nat.ofDigits 10 [9, 8, E, 7, 6, 7] := by rfl
      rw [this] at h
      have h := (Nat.nine_dvd_iff (Nat.ofDigits 10 [9, 8, E, 7, 6, 7])).mp h
      have : Nat.digits 10 (Nat.ofDigits 10 [9, 8, E, 7, 6, 7]) = [9, 8, E, 7, 6, 7] := by
        apply Nat.digits_ofDigits 10 (by norm_num) [9, 8, E, 7, 6, 7]
        simp
        use (by linarith)
        simp
      rw [this] at h
      have : [9, 8, E, 7, 6, 7].sum = 37 + D + E := by
        simp
        linarith
      rw [this] at h
      exact h
    have h := (Nat.nine_dvd_iff (Nat.ofDigits 10 [9, 8, E, 7, 6, 7, D])).mp h
    have : Nat.digits 10 (Nat.ofDigits 10 [9, 8, E, 7, 6, 7, D]) = [9, 8, E, 7, 6, 7, D] := by
      apply Nat.digits_ofDigits 10 (by norm_num) [9, 8, E, 7, 6, 7, D]
      simp
      use (by linarith)
      simp
      exact hD₀
    rw [this] at h
    have : [9, 8, E, 7, 6, 7, D].sum = 37 + D + E := by
      simp
      linarith
    rw [this] at h
    exact h

  -- Since $D$ and $E$ are each a single digit, we know each is between $0$ and $9.$
  -- Therefore, $D+E$ is between $0$ and $18.$ Therefore, $37+D+E$ is between $37$ and $55.$
  have hDE₁: 37 + D + E ≤ 55 := by omega
  have hDE₀: 37 ≤ 37 + D + E := by omega
  -- The numbers between $37$ and $55$ that are divisible by $9$ are $45$ and $54.$
  have : ∀n, 37 ≤ n ∧ n ≤ 55 → 9 ∣ n → n = 45 ∨ n = 54 := by omega
  simp at this
  constructor
  . obtain (r | r) := this (37 + D + E) hDE₀ hDE₁ h
    . -- If $37+D+E=45,$ then $D+E=8.$
      exact Or.inl (by linarith)
    . -- If $37+D+E=54,$ then $D+E=17.$
      exact Or.inr (by linarith)
  -- Therefore, the possible values of $D+E$ are $8$ and $17.$ Our answer is then $8+17=\boxed{25}.$
  . -- 8+17=25
    norm_num
