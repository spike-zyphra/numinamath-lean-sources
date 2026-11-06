import Mathlib

def is_kawaii_sequence (a : ℕ → ℤ) := a 0 = 0 ∧ a 1 = 1 ∧ ∀ n, (a (n + 2) - 3 * a (n + 1) + 2 * a n) * (a (n + 2) - 4 * a (n + 1) + 3 * a n) = 0

def is_kawaii (x : ℤ) := ∃ a : ℕ → ℤ, is_kawaii_sequence a ∧ ∃ n, a n = x

/- A sequence of integers $a_{0}, a_{1}, a_{2}, \ldots$ is called kawaii, if $a_{0}=0, a_{1}=1$, and, for any positive integer $n$, we have  $$ \left(a_{n+1}-3 a_{n}+2 a_{n-1}\right)\left(a_{n+1}-4 a_{n}+3 a_{n-1}\right)=0 . $$  An integer is called kawaii if it belongs to a kawaii sequence. Suppose that two consecutive positive integers $m$ and $m+1$ are both kawaii (not necessarily belonging to the same kawaii sequence). Prove that 3 divides $m$, and that $m / 3$ is kawaii. (China) -/
theorem algebra_607760 (m : ℤ) (hmpos : m > 0) (hm₁ : is_kawaii m) (hm₂ : is_kawaii (m + 1)) : 3 ∣ m ∧ is_kawaii (m / 3) := by
  -- Lemma 1: A kawaii sequence satisfies $a_{n+2} \equiv a_{n+1} \pmod{2}$ or $a_{n+2} \equiv a_{n} \pmod{2}$ for all $n$.
  have H₁ {a : ℕ → ℤ} (h : is_kawaii_sequence a) (n : ℕ) :
      a (n + 2) ≡ a (n + 1) [ZMOD 2] ∨ a (n + 2) ≡ a n [ZMOD 2] := by
    rcases h with ⟨ha₀, ha₁, ha⟩
    obtain ha | ha := mul_eq_zero.mp (ha n)
    . left
      rw [Int.modEq_iff_dvd]
      omega
    . right
      rw [Int.modEq_iff_dvd]
      omega
  -- Lemma 2: A kawaii sequence satisfies $a_{n+2} \equiv a_{n+1} \pmod{3}$ or $a_{n+2} \equiv a_{n} \pmod{3}$ for all $n$.
  have H₂ {a : ℕ → ℤ} (h : is_kawaii_sequence a) (n : ℕ) :
    a (n + 2) ≡ a (n + 1) [ZMOD 3] ∨ a (n + 2) ≡ a n [ZMOD 3] := by
    rcases h with ⟨ha₀, ha₁, ha⟩
    obtain ha | ha := mul_eq_zero.mp (ha n)
    . right
      rw [Int.modEq_iff_dvd]
      omega
    . left
      rw [Int.modEq_iff_dvd]
      omega
  -- Lemma 3: A kawaii integer is congruent to 0 or 1 modulo 3.
  have H₃ {x : ℤ} (h : is_kawaii x) : x ≡ 0 [ZMOD 3] ∨ x ≡ 1 [ZMOD 3] := by
    -- Consider the cases of $x \pmod{3}$.
    mod_cases hx : x % 3
    . simp [hx]
    . simp [hx]
    . -- $x \equiv 2 \pmod{3}$ contradicts with lemma 2.
      rcases h with ⟨a, h, n, rfl⟩
      absurd hx
      clear * - h H₂
      specialize H₂ h
      induction n using Nat.twoStepInduction with
      | zero => simp [h.1]; decide
      | one => simp [h.2]; decide
      | more n ih₁ ih₂ =>
        rcases H₂ n with h₁ | h₁
        . intro h₂
          exact ih₂ (h₁.symm.trans h₂)
        . intro h₂
          exact ih₁ (h₁.symm.trans h₂)
  -- Lemma 4: A kawaii sequence satisfies $a_{2}=3$ or $a_{2}=4$.
  -- Moreover, if $a_{2}=3$, then $a_{n} \equiv 1 \pmod{2}$ for all $n \geq 1$. (1)
  -- If $a_{2}=4$, then $a_{n} \equiv 1 \pmod{3}$ for all $n \geq 1$. (2)
  have H₄ {a : ℕ → ℤ} (h : is_kawaii_sequence a) : (a 2 = 3 ∧ ∀ n ≥ 1, a n ≡ 1 [ZMOD 2]) ∨ (a 2 = 4 ∧ ∀ n ≥ 1, a n ≡ 1 [ZMOD 3]) := by
    rcases h with ⟨ha₀, ha₁, ha⟩
    obtain ha₂ | ha₂ := mul_eq_zero.mp (ha 0)
    . simp [ha₀, ha₁, sub_eq_zero] at ha₂
      refine Or.inl ⟨ha₂, fun n hn => ?_⟩
      -- Two step induction.
      suffices a n ≡ 1 [ZMOD 2] ∧ a (n + 1) ≡ 1 [ZMOD 2] from this.1
      induction n, hn using Nat.le_induction with
      | base => simp [ha₁, ha₂]; decide
      | succ n hn ih =>
        rcases ih with ⟨ih₁, ih₂⟩
        use ih₂
        rcases H₁ ⟨ha₀, ha₁, ha⟩ n with h₁ | h₁
        . exact h₁.trans ih₂
        . exact h₁.trans ih₁
    . simp [ha₀, ha₁, sub_eq_zero] at ha₂
      refine Or.inr ⟨ha₂, fun n hn => ?_⟩
      -- Two step induction.
      suffices a n ≡ 1 [ZMOD 3] ∧ a (n + 1) ≡ 1 [ZMOD 3] from this.1
      induction n, hn using Nat.le_induction with
      | base => simp [ha₁, ha₂]; decide
      | succ n hn ih =>
        rcases ih with ⟨ih₁, ih₂⟩
        use ih₂
        rcases H₂ ⟨ha₀, ha₁, ha⟩ n with h₁ | h₁
        . exact h₁.trans ih₂
        . exact h₁.trans ih₁
  -- Back to the problem.
  -- We first show that $3$ divides $m$.
  -- Since both $m$ and $m+1$ are kawaii, we can apply lemma 3 to get $m \equiv 0 \pmod{3}$.
  have hm : 3 ∣ m := by
    mod_cases m % 3
    . exact Int.dvd_of_emod_eq_zero H
    . rcases H₃ hm₂ with h₁ | h₁
      . rw [Int.ModEq] at H h₁
        omega
      . rw [Int.ModEq] at H h₁
        omega
    . rcases H₃ hm₁ with h₁ | h₁
      . rw [Int.ModEq] at H h₁
        omega
      . rw [Int.ModEq] at H h₁
        omega
  use hm
  -- We extract the kawaii sequences from $m$ and $m+1$.
  rcases hm with ⟨k, hk⟩
  rcases hm₁ with ⟨a₁, h₁, n₁, hn₁⟩
  rcases hm₂ with ⟨a₂, h₂, n₂, hn₂⟩
  -- We show that $n_1$ and $n_2$ are positive.
  -- This is because $m$ is positive.
  have hn₁pos : n₁ ≥ 1 := by
    by_contra h₄
    simp at h₄
    simp [h₄, h₁.1] at hn₁
    linarith only [hn₁, hmpos]
  have hn₂pos : n₂ ≥ 1 := by
    by_contra h₄
    simp at h₄
    simp [h₄, h₂.1] at hn₂
    linarith only [hn₂, hmpos]
  -- We show that $m$ is odd.
  -- This is because $a_1$ does not satisfy (2), so it must satisfy (1).
  have hm : Odd m := by
    obtain ⟨-, h₃⟩ | ⟨-, h₃⟩ := H₄ h₁
    . specialize h₃ n₁ hn₁pos
      exact hn₁ ▸ Int.odd_iff.mpr h₃
    . specialize h₃ n₁ hn₁pos
      simp [hn₁, hk, Int.ModEq] at h₃
  -- We show that $a_2$ satisfies (2), since it does not satisfy (1).
  have h₃ : a₂ 2 = 4 ∧ ∀ n ≥ 1, a₂ n ≡ 1 [ZMOD 3] := by
    refine (or_iff_right fun h => ?_).mp (H₄ h₂)
    rcases h with ⟨-, h⟩
    specialize h n₂ hn₂pos
    rw [hn₂] at h
    clear * - hm h
    have hm' : Even (m + 1) := Odd.add_one hm
    have h' : Odd (m + 1) := Int.odd_iff.mpr h
    exact Int.not_odd_iff_even.mpr hm' h'
  -- We can now define the sequence $a_3$
  let a₃ (n : ℕ) := (a₂ (n + 1) - 1) / 3
  have h₄ (n : ℕ) : a₂ (n + 1) = a₃ n * 3 + 1 := by
    simp [a₃]
    rw [← sub_eq_iff_eq_add]
    refine (Int.ediv_mul_cancel ?_).symm
    rw [← Int.modEq_iff_dvd]
    exact (h₃.2 (n + 1) (by simp)).symm
  -- We show that $a_3$ is a kawaii sequence.
  -- The recurrence relation follows from that of $a_2$.
  -- The initial values are also satisfied.
  have h₅ : is_kawaii_sequence a₃ := by
    refine ⟨?_, ?_, ?_⟩
    . simp [a₃, h₂.2]
    . simp [a₃, h₃.1]
    . intro n
      have h₅ := h₂.2.2 (n + 1)
      rw [show n + 1 + 2 = n + 2 + 1 by ring, h₄, h₄, h₄] at h₅
      linarith only [h₅]
  -- The $n_2-1$-th term of $a_3$ is $m/3$.
  use a₃, h₅, n₂ - 1
  simp [a₃, hn₂pos, hn₂]
