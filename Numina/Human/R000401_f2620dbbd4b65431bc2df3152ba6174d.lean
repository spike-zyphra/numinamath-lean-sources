import Mathlib

/-The greatest integer function, $\lfloor x\rfloor$, denotes the largest integer less than or equal to $x$. For example, $\lfloor3.5\rfloor=3$, $\lfloor\pi\rfloor=3$ and $\lfloor -\pi\rfloor=-4$. Find the sum of the three smallest positive solutions to $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor}.$ Express your answer as a mixed number.-/
theorem algebra_10188 (hf : f = fun x : ℝ => x - ⌊x⌋ = 1 / ⌊x⌋ ) :
  f (2 + 1 / 2) ∧  f (3 + 1 / 3) ∧ f (4 + 1 / 4) ∧ (∀ x, 0 < x → f x → 2 + 1 / 2 ≤ x)
  ∧ (∀ x, 0 < x → f x → 2 + 1 / 2 < x → 3 + 1 / 3 ≤ x) ∧ (∀ x, 0 < x → f x → 3 + 1 / 3 < x → 4 + 1 / 4 ≤ x)
  ∧ (2 + (1 : ℝ) / 2) + (3 + 1 / 3) + (4 + 1 / 4) = 10 + 1 / 12 := by
    -- if postive real number $x$ satisfy the equation $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor}.$ There exist a positive integer number which greater than 2 such that $x = n + \frac 1 n$ 
    have faux : ∀ x, 0 < x → f x → ∃ n : ℤ, 2 ≤ n ∧ x = n + 1 / n := by
      intro x xpos fx
      simp only [hf] at fx
      have : 2 < x := by
        by_contra!
        by_cases x2 : x = 2
        · simp [x2] at fx
        · by_cases xlt1 : x < 1
          · have : ⌊x⌋ = 0 :=  Int.floor_eq_zero_iff.mpr (by simp; split_ands <;> linarith)
            simp [this] at fx
            linarith
          · simp at xlt1
            have : x < 2 :=  lt_of_le_of_ne this x2
            have : ⌊x⌋ = 1 := Int.floor_eq_iff.mpr (by simp; split_ands <;> linarith)
            simp [this] at fx
            linarith
      have xfloorge2 : 2 ≤ ⌊x⌋ := Int.le_floor.mpr (by simp; linarith)
      use ⌊x⌋
      exact ⟨xfloorge2, by linarith⟩
    -- auxiliary lemma : for integer number which greater than 1, `⌊(n : ℝ) + 1 / n⌋ = n`.
    have aux (n : ℤ) (hn : 1 < n) : ⌊(n : ℝ) + 1 / n⌋ = n := by
      simp
      exact ⟨by linarith, by
        field_simp; apply (one_div_lt (by simp) (by simp; linarith) ).1; simp; norm_cast⟩
    split_ands
    · -- Verify that 2 + 1 / 2 satisfies the equation $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor}
      simp only [hf]
      rw [show ⌊(2 : ℝ) + 1 / 2⌋ = 2 by convert aux 2 (by linarith) ]
      simp
    · -- Verify that 3 + 1 / 3 satisfies the equation $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor}
      simp only [hf]
      rw [show ⌊(3 : ℝ) + 1 / 3⌋ = 3 by convert aux 3 (by linarith) ]
      simp
    · -- -- Verify that 4 + 1 / 4 satisfies the equation $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor}
      simp only [hf]
      rw [show ⌊(4 : ℝ) + 1 / 4⌋ = 4 by convert aux 4 (by linarith) ]
      simp
    -- Prove that three smallest positive solutions to $x-\lfloor x\rfloor=\frac1{\lfloor x\rfloor} are 2 + 1 / 2, 3 + 1 / 3 and 4 + 1 / 4.
    · intro x xpos fx
      obtain ⟨n, hn⟩ := faux x xpos fx
      rw [hn.2]
      by_cases n2 : n = 2
      · simp [n2]
      · have ngt2 : 2 < n := lt_of_le_of_ne hn.1 (by simp; tauto)
        have c1 : (3 : ℝ) ≤ n := by norm_cast
        have c2 : (2 : ℝ)+ 1 / 2 ≤ 3 := by linarith
        have := c2.trans c1
        exact this.trans (by simp; linarith)
    · intro x xpos fx xgt
      obtain ⟨n, hn⟩ := faux x xpos fx
      rw [hn.2]
      have nge3 : 3 ≤ n := by
        rw [hn.2] at xgt
        by_contra!
        have : n = 2 := by omega
        simp [this] at xgt
      by_cases n3 : n = 3
      · simp [n3]
      · have : 3 < n := by omega
        have c1 : (4 : ℝ) ≤ n := by norm_cast
        calc
          _ ≤ (4 : ℝ) := by linarith
          _ ≤ n := c1
          _ ≤ _ := by simp; linarith
    · intro x xpos fx xgt
      obtain ⟨n, hn⟩ := faux x xpos fx
      rw [hn.2] at  xgt ⊢
      have nge4 : 4 ≤ n := by
        by_contra!
        have := hn.1
        interval_cases n <;> simp at xgt
        field_simp at xgt
        linarith
      by_cases n4 : n = 4
      · simp [n4]
      · have : 4 < n := by omega
        have c1 : (5 : ℝ) ≤ n := by norm_cast
        calc
          _ ≤ (5 : ℝ) := by linarith
          _ ≤ n := c1
          _ ≤ _ := by simp; linarith
    · -- Check that the sum of them is 10 + 1 / 12
      linarith
