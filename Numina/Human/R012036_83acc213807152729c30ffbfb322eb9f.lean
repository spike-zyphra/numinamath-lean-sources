import Mathlib

/- Example 3 Suppose the lengths of the two legs of a right triangle are $a$ and $b$, and the length of the hypotenuse is $c$. If $a$, $b$, and $c$ are all positive integers, and $c=\frac{1}{3} a b-(a+b)$, find the number of right triangles that satisfy the condition.
(2010, National Junior High School Mathematics Competition, Tianjin Preliminary Round) -/
theorem number_theory_325455 :
  { (a, b, c) : ℕ × ℕ × ℕ
  | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≤ b
    ∧ a^2 + b^2 = c^2
    ∧ (c : ℚ) = (1/3)*a*b - (a+b)
  }.ncard = 3 :=
by
  -- We prove the goal by calculating each answer.
  have :
    { (a, b, c) : ℕ × ℕ × ℕ
    | a > 0 ∧ b > 0 ∧ c > 0 ∧ a ≤ b
      ∧ a^2 + b^2 = c^2
      ∧ (c : ℚ) = (1/3)*a*b - (a+b)
    } = {(7,24,25), (8,15,17), (9,12,15)} :=
  by
    ext ⟨a,b,c⟩
    constructor; swap
    . -- Simply verify each answer
      simp
      rintro (h|h|h)
      <;> rcases h with ⟨aa,bb,cc⟩
      <;> subst aa bb cc
      <;> repeat (constructor; try tauto)
      all_goals ring_nf
    . -- We will get the answer by solving the integer equation
      -- $(a - 6) (b - 6) = 18$
      -- First we see how to get the equation.
      simp
      intro apos bpos cpos aleb H1 H2
      apply_fun (fun x => x ^ 2) at H2
      have H1' := H1
      qify at H1'
      have := Eq.trans H1' H2
      have : (a * b - 6 * (a + b) + 18 : ℤ) = 0 := by
        qify
        apply_fun (fun (x : ℚ) => x - a^2 - b^2) at this
        ring_nf at this
        cancel_denoms at this
        apply_fun (fun (x : ℚ) => x / (a * b)) at this
        have h : (a * b : ℚ) > 0 := by
          qify at apos bpos
          apply Left.mul_pos
          assumption
          assumption
        have h1 : (0 : ℚ) / (a * b) = 0 := by field_simp
        rw[h1] at this
        have h2 : (a*b*18 + -(a*b^2*6) + -(a^2*b*6)+a^2*b^2 : ℚ)/(a*b)
                = 18 - b*6 - a*6 + a*b:= by
          field_simp
          ring_nf
        rw [h2] at this
        linarith
      have H : ((a - 6) * (b - 6) : ℤ) = 18 := by
        ring_nf
        linarith
      have : (a - 6 : ℤ) > 0 ∧ (b - 6 : ℤ) > 0 := by
        by_contra h
        push_neg at h
        rcases em ((a - 6 : ℤ) > 0) with (h'|h')
        . have := h h'
          have : ((a - 6) * (b - 6) : ℤ) ≤ 0 := by linarith
          rw [H] at this
          simp at this
        . push_neg at h'
          rcases em ((b - 6 : ℤ) > 0) with (h''|h'')
          . have : ((a - 6) * (b - 6) : ℤ) ≤ 0 := by
              apply Int.mul_nonpos_of_nonpos_of_nonneg h'
              apply Int.le_of_lt
              assumption
            rw [H] at this
            simp at this
          . push_neg at h''
            have bu : a ≤ 6 := by omega
            have au : b ≤ 6 := by omega
            interval_cases a <;> interval_cases b
            <;> simp at H
      -- Using a' stand for a - 6
      -- we will iterate on a' and b' later.
      let a' := a - 6
      let b' := b - 6
      have a6 : a > 6 := by zify; linarith
      have b6 : b > 6 := by zify; linarith
      have a'b' : a' * b' = 18 := by
        cases this
        simp [a', b']
        have : (a - 6 : ℤ) = (a - 6 : ℕ) := by omega
        zify
        rw [←this]
        have : (b - 6 : ℤ) = (b - 6 : ℕ) := by omega
        rw [←this]
        assumption
      have : b' ≤ 18 := by
        have : b' ∣ 18 := by use a'; rw [mul_comm]; omega
        apply Nat.le_of_dvd
        simp
        assumption
      have : a' ≤ b' := by
        simp [a', b']
        rw [Nat.sub_add_cancel]
        assumption
        omega
      have c_def' : c = Nat.sqrt (a ^ 2 + b ^ 2) := by
        rw [show c ^ 2 = c * c by linarith] at H1
        rw [H1]
        symm
        apply Nat.sqrt_eq
      have a_def : a = a' + 6 := by omega
      have b_def : b = b' + 6 := by omega
      have c_def : c = Nat.sqrt ((a' + 6) ^ 2 + (b' + 6) ^ 2) := by
        rw [c_def', a_def, b_def]
      -- Try each possible values of a' and b'
      interval_cases b'
      <;> interval_cases a'
      <;> try simp at a'b'
      . simp at a_def b_def c_def
        have : c = 15 := by
          have : 15 * 15 = 225 := by simp
          have : Nat.sqrt 225 = 15 := by
            rw [←this]
            apply Nat.sqrt_eq
          rw [this] at c_def
          assumption
        rw [this, a_def, b_def]
        decide
      -- Now we manually handle the remaining three correct cases,
      -- so we can bypass the square root calculation and speed up the checking
      . simp at a_def b_def c_def
        have : c = 17 := by
          have : 17 * 17 = 289 := by simp
          have : Nat.sqrt 289 = 17 := by
            rw [←this]
            apply Nat.sqrt_eq
          rw [this] at c_def
          assumption
        rw [this, a_def, b_def]
        decide
      . simp at a_def b_def c_def
        have : c = 25 := by
          have : 25 * 25 = 625 := by simp
          have : Nat.sqrt 625 = 25 := by
            rw [←this]
            apply Nat.sqrt_eq
          rw [this] at c_def
          exact c_def
        rw [this, a_def, b_def]
        decide
  rw [this]
  simp
