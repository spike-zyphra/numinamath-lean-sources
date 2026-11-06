import Mathlib

/- 2. (Reverse Induction) If:
（1）Conclusion P holds for infinitely many natural numbers $n$,
（2）From P holding for a natural number $n(n \geqslant 2)$, it can be deduced that P also holds for $n-1$,
then Conclusion P holds for all natural numbers. -/
theorem number_theory_7301 (P : ℕ → Prop) (hP : ∀ n, 2 ≤ n → P n → P (n - 1)) (hP' : {n | P n}.Infinite) : ∀ n≥ 1, P n := by

  -- We prove that if conclusion P holds for some number, it holds for all the numbers smaller than it.
  have lem: ∀ k:ℕ, ∀ a b :ℕ, (1≤ a ∧ b=a+k ∧ P b) → P a := by
    intro k
    induction' k with k hk

    --the case k = 0
    intro a b ⟨age1, bmaek, Pb⟩
    have : a = b := by linarith
    rw [this]
    assumption

    intro a b ⟨age1, bmaek, Pb⟩
    have : P (a+1) := by
      apply hk (a+1) b
      constructor
      linarith
      constructor
      linarith
      exact Pb
    have : P a := by
      apply hP (a+1)
      linarith
      exact this
    exact this
  
  --Since there are infinite numbers satisfies $P$, we choose some number large enough and get our conclusion.
  intro n hn
  rw [Set.infinite_iff_exists_gt] at hP'
  specialize hP' n
  simp at hP'
  obtain ⟨b, Pb, nlb⟩ := hP'
  have : ∃ k : ℕ, b = n + k := by use b-n; omega
  obtain ⟨k,hk⟩ := this
  apply lem k n b
  constructor
  linarith
  tauto
