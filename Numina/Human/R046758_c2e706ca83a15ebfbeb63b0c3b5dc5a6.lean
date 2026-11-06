import Mathlib

/-- The sequence $a$ is defined by the relations $a_{1}=1$,
$$ a_{2 n}=\left\{\begin{array}{ll}
a_{n}, & \text { if } n \text { is even, } \\
2 a_{n}, & \text { if } n \text { is odd; }
\end{array} \quad a_{2 n+1}= \begin{cases}2 a_{n}+1, & \text { if } n \text { is even, } \\
a_{n}, & \text { if } n \text { is odd. }\end{cases}\right. $$
Find the smallest natural $n$ for which $a_{n}=a_{2017}$. -/
theorem number_theory_198437 (a : ℕ → ℕ)
    (h₀ : a 1 = 1)
    (h₁ : ∀ n, Even n → a (2 * n) = a n)
    (h₂ : ∀ n, Odd n → a (2 * n) = 2 * a n)
    (h₃ : ∀ n, Even n → a (2 * n + 1) = 2 * a n + 1)
    (h₄ : ∀ n, Odd n → a (2 * n + 1) = a n) :
    IsLeast {n | 0 < n ∧ a n = a 2017} 5 := by
  -- We have a_{2017} = 5:
  have : a 2017 = 5 := by
    -- a_{2017}  = 2a_{1008} + 1
    calc a 2017 = 2 * a 1008 + 1 := by rw[h₃ 1008 ⟨504,rfl⟩]
              -- = 2a_{504} + 1
              _ = 2 * a 504 + 1 := by rw[h₁ 504 ⟨252,rfl⟩]
              -- = 2a_{252} + 1
              _ = 2 * a 252 + 1 := by rw[h₁ 252 ⟨126,rfl⟩]
              -- = 2a_{126} + 1
              _ = 2 * a 126 + 1 := by rw[h₁ 126 ⟨63,rfl⟩]
              -- = 2 * 2 * a_{63} + 1
              _ = 2 * (2 * a 63) + 1 := by rw[h₂ 63 ⟨31,rfl⟩]
              -- = 2 * 2 * a_{31} + 1
              _ = 2 * (2 * a 31) + 1 := by rw[h₄ 31 ⟨15,rfl⟩]
              -- = 2 * 2 * a_{15} + 1
              _ = 2 * (2 * a 15) + 1 := by rw[h₄ 15 ⟨7,rfl⟩]
              -- = 2 * 2 * a_{7} + 1
              _ = 2 * (2 * a 7) + 1 := by rw[h₄ 7 ⟨3,rfl⟩]
              -- = 2 * 2 * a_{3} + 1
              _ = 2 * (2 * a 3) + 1 := by rw[h₄ 3 ⟨1,rfl⟩]
              -- = 2 * 2 * a_{1} + 1
              _ = 2 * (2 * a 1) + 1 := by rw[h₄ 1 ⟨0,rfl⟩]
              -- = 2 * 2 * 1 + 1 = 5.
              _ = 2 * 2 + 1 := by rw[h₀]
  rw[this]
  constructor
  · rw[Set.mem_setOf_eq]
    -- Now a_5 = 2*a_2 + 1 = 2 * 2 * a_1 + 1 = 2 * 2 * 1 + 1 = 5.
    apply And.intro (by simp)
    calc a 5 = 2 * a 2 + 1 := by rw[h₃ 2 ⟨1,rfl⟩]
           _ = 2 * (2 * a 1) + 1 := by rw[h₂ 1 ⟨0,rfl⟩]
           _ = 2 * 2 + 1 := by rw[h₀]
    -- Hence it only remains to be shown that a_1,...a_4 ≠ 5.
  · rintro m ⟨gt,val⟩
    by_contra! lt
    interval_cases m
    -- a_1 = 1 ≠ 5 by assumption.
    · rw[h₀] at val; contradiction
    -- a_2 = 2a_1 = 2 ≠ 5.
    · rw[h₂ 1 ⟨0,rfl⟩, h₀] at val; contradiction
    -- a_3 = a_1 = 1 ≠ 5.
    · rw[h₄ 1 ⟨0,rfl⟩, h₀] at val; contradiction
    -- a_4 = a_2 = 2 ≠ 5.
    · rw[h₁ 2 ⟨1,rfl⟩, h₂ 1 ⟨0,rfl⟩, h₀] at val; contradiction